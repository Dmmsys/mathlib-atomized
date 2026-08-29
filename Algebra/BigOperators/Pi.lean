/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.FunLike.IsApply

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary products
of monoids and groups.
-/

@[expose] public section

open scoped Finset

variable {ι κ M N R α : Type*}

namespace Pi

@[to_additive]
/--
theorem `list_prod_apply` / 定理 `list_prod_apply`

English:
theorem list_prod_apply
  statement: {α : Type*} {M : α -> Type*} [forall a, Monoid (M a)] (a : α)
  proof: map_list_prod (evalMonoidHom M a) _

@[to_additive]

中文:
定理 list_prod_apply
  结论: {α : 类型} {M : α -> 类型} [对任意 a, 幺半群 (M a)] (a : α)
  证明: map_list_prod (evalMonoidHom M a) _

@[to_additive]

Depends on / 依赖: evalMonoidHom, map_list_prod
-/
theorem list_prod_apply {α : Type*} {M : α -> Type*} [forall a, Monoid (M a)] (a : α)
    (l : List (forall a, M a)) : l.prod a = (l.map fun f : forall a, M a => f a).prod :=
  map_list_prod (evalMonoidHom M a) _

@[to_additive]
/--
theorem `multiset_prod_apply` / 定理 `multiset_prod_apply`

English:
theorem multiset_prod_apply
  statement: {α : Type*} {M : α -> Type*} [forall a, CommMonoid (M a)] (a : α)
  proof: (evalMonoidHom M a).map_multiset_prod _

中文:
定理 multiset_prod_apply
  结论: {α : 类型} {M : α -> 类型} [对任意 a, 交换幺半群 (M a)] (a : α)
  证明: (evalMonoidHom M a).map_multiset_prod _

Depends on / 依赖: evalMonoidHom, map_multiset_prod
-/
theorem multiset_prod_apply {α : Type*} {M : α -> Type*} [forall a, CommMonoid (M a)] (a : α)
    (s : Multiset (forall a, M a)) : s.prod a = (s.map fun f : forall a, M a => f a).prod :=
  (evalMonoidHom M a).map_multiset_prod _

end Pi

@[to_additive (attr := simp)]
/--
theorem `Finset.prod_apply` / 定理 `Finset.prod_apply`

English:
theorem Finset.prod_apply
  statement: {α : Type*} {M : α -> Type*} [forall a, CommMonoid (M a)] (a : α)
  proof: map_prod (Pi.evalMonoidHom M a) _ _

中文:
定理 有限集.prod_apply
  结论: {α : 类型} {M : α -> 类型} [对任意 a, 交换幺半群 (M a)] (a : α)
  证明: map_prod (Pi.evalMonoidHom M a) _ _

Depends on / 依赖: Pi.evalMonoidHom, evalMonoidHom, map_prod
-/
theorem Finset.prod_apply {α : Type*} {M : α -> Type*} [forall a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in s, g c) a = ∏ c in s, g c a :=
  map_prod (Pi.evalMonoidHom M a) _ _

/-- An 'unapplied' analogue of `Finset.prod_apply`. -/
@[to_additive (attr := push ←) /-- An 'unapplied' analogue of `Finset.sum_apply`. -/]
/--
theorem `Finset.prod_fn` / 定理 `Finset.prod_fn`

English:
theorem Finset.prod_fn
  statement: {α : Type*} {M : α -> Type*} {ι} [forall a, CommMonoid (M a)] (s : Finset ι)
  proof: funext fun _ => Finset.prod_apply _ _ _

@[to_additive]

中文:
定理 有限集.prod_fn
  结论: {α : 类型} {M : α -> 类型} {ι} [对任意 a, 交换幺半群 (M a)] (s : 有限集 ι)
  证明: funext fun _ => Finset.prod_apply _ _ _

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_apply, prod_apply
-/
theorem Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall a, CommMonoid (M a)] (s : Finset ι)
    (g : ι -> forall a, M a) : ∏ c in s, g c = fun a => ∏ c in s, g c a :=
  funext fun _ => Finset.prod_apply _ _ _

@[to_additive]
/--
theorem `Fintype.prod_apply` / 定理 `Fintype.prod_apply`

English:
theorem Fintype.prod_apply
  statement: {α : Type*} {M : α -> Type*} [Fintype ι] [forall a, CommMonoid (M a)] (a : α)
  proof: Finset.prod_apply a Finset.univ g

@[to_additive prod_mk_sum]

中文:
定理 有限类型.prod_apply
  结论: {α : 类型} {M : α -> 类型} [有限类型 ι] [对任意 a, 交换幺半群 (M a)] (a : α)
  证明: Finset.prod_apply a Finset.univ g

@[to_additive prod_mk_sum]

Depends on / 依赖: Finset, Finset.prod_apply, Finset.univ, prod_apply
-/
theorem Fintype.prod_apply {α : Type*} {M : α -> Type*} [Fintype ι] [forall a, CommMonoid (M a)] (a : α)
    (g : ι -> forall a, M a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g

@[to_additive prod_mk_sum]
/--
theorem `prod_mk_prod` / 定理 `prod_mk_prod`

English:
theorem prod_mk_prod
  given: [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι -> M) (g : ι -> N)
  proof: haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

中文:
定理 prod_mk_prod
  条件: [交换幺半群 M] [交换幺半群 N] (s : 有限集 ι) (f : ι -> M) (g : ι -> N)
  证明: haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, Prod.ext_iff, contextual, ext_iff, induction_on
-/
theorem prod_mk_prod [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι -> M) (g : ι -> N) :
    (∏ x in s, f x, ∏ x in s, g x) = ∏ x in s, (f x, g x) :=
  haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

/--
theorem `pi_eq_sum_univ` / 定理 `pi_eq_sum_univ`

English:
theorem pi_eq_sum_univ
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
  proof: by
  ext
  simp

中文:
定理 pi_eq_sum_univ
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι] {R : 类型} [非结合半环 R]
  证明: by
  ext
  simp
-/
theorem pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι -> R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) else 0 := by
  ext
  simp

/--
theorem `pi_eq_sum_univ'` / 定理 `pi_eq_sum_univ'`

English:
theorem pi_eq_sum_univ'
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
  proof: by
  convert! pi_eq_sum_univ x
  aesop

中文:
定理 pi_eq_sum_univ'
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι] {R : 类型} [非结合半环 R]
  证明: by
  convert! pi_eq_sum_univ x
  aesop

Depends on / 依赖: convert, pi_eq_sum_univ
-/
theorem pi_eq_sum_univ' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι -> R) : x = ∑ i, (x i) • Pi.single (M := fun _ => R) i 1 := by
  convert! pi_eq_sum_univ x
  aesop

section CommSemiring
variable [CommSemiring R]

/--
lemma `prod_indicator_apply` / 引理 `prod_indicator_apply`

English:
lemma prod_indicator_apply
  given: (s : Finset ι) (f : ι -> Set κ) (g : ι -> κ -> R) (j : κ)
  proof: by
  rw [Set.indicator]
  split_ifs with hj
  · rw [Finset.prod_apply]
    congr! 1 with i hi
    simp only [Set.mem_iInter] at hj
    exact Set.indicator_of_mem (hj _ hi) _
  · obtain ⟨i, hi, hj⟩ := by simpa using hj
exact Finset.prod_eq_zero hi Set.indicator_of_notMem hj _

中文:
引理 prod_indicator_apply
  条件: (s : 有限集 ι) (f : ι -> 集合 κ) (g : ι -> κ -> R) (j : κ)
  证明: by
  rw [Set.indicator]
  split_ifs with hj
  · rw [Finset.prod_apply]
    congr! 1 with i hi
    simp only [Set.mem_iInter] at hj
    exact Set.indicator_of_mem (hj _ hi) _
  · obtain ⟨i, hi, hj⟩ := by simpa using hj
exact Finset.prod_eq_zero hi Set.indicator_of_notMem hj _

Depends on / 依赖: Finset, Finset.prod_apply, Finset.prod_eq_zero, Set.indicator, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_iInter, indicator, indicator_of_mem, indicator_of_notMem, mem_iInter, prod_apply, prod_eq_zero, split_ifs
-/
lemma prod_indicator_apply (s : Finset ι) (f : ι -> Set κ) (g : ι -> κ -> R) (j : κ) :
    ∏ i in s, (f i).indicator (g i) j = (⋂ x in s, f x).indicator (∏ i in s, g i) j := by
  rw [Set.indicator]
  split_ifs with hj
  · rw [Finset.prod_apply]
    congr! 1 with i hi
    simp only [Set.mem_iInter] at hj
    exact Set.indicator_of_mem (hj _ hi) _
  · obtain ⟨i, hi, hj⟩ := by simpa using hj
exact Finset.prod_eq_zero hi Set.indicator_of_notMem hj _

/--
lemma `prod_indicator` / 引理 `prod_indicator`

English:
lemma prod_indicator
  given: (s : Finset ι) (f : ι -> Set κ) (g : ι -> κ -> R)
  proof: by
  ext a; simpa using prod_indicator_apply ..

中文:
引理 prod_indicator
  条件: (s : 有限集 ι) (f : ι -> 集合 κ) (g : ι -> κ -> R)
  证明: by
  ext a; simpa using prod_indicator_apply ..

Depends on / 依赖: prod_indicator_apply
-/
lemma prod_indicator (s : Finset ι) (f : ι -> Set κ) (g : ι -> κ -> R) :
    ∏ i in s, (f i).indicator (g i) = (⋂ x in s, f x).indicator (∏ i in s, g i) := by
  ext a; simpa using prod_indicator_apply ..

/--
lemma `prod_indicator_const_apply` / 引理 `prod_indicator_const_apply`

English:
lemma prod_indicator_const_apply
  given: (s : Finset ι) (f : ι -> Set κ) (g : κ -> R) (j : κ)
  proof: by
  simp [prod_indicator_apply]

中文:
引理 prod_indicator_const_apply
  条件: (s : 有限集 ι) (f : ι -> 集合 κ) (g : κ -> R) (j : κ)
  证明: by
  simp [prod_indicator_apply]

Depends on / 依赖: prod_indicator_apply
-/
lemma prod_indicator_const_apply (s : Finset ι) (f : ι -> Set κ) (g : κ -> R) (j : κ) :
    ∏ i in s, (f i).indicator g j = (⋂ x in s, f x).indicator (g ^ #s) j := by
  simp [prod_indicator_apply]

/--
lemma `prod_indicator_const` / 引理 `prod_indicator_const`

English:
lemma prod_indicator_const
  given: (s : Finset ι) (f : ι -> Set κ) (g : κ -> R)
  proof: by simp [prod_indicator]

中文:
引理 prod_indicator_const
  条件: (s : 有限集 ι) (f : ι -> 集合 κ) (g : κ -> R)
  证明: by simp [prod_indicator]

Depends on / 依赖: prod_indicator
-/
lemma prod_indicator_const (s : Finset ι) (f : ι -> Set κ) (g : κ -> R) :
    ∏ i in s, (f i).indicator g = (⋂ x in s, f x).indicator (g ^ #s) := by simp [prod_indicator]

end CommSemiring

section MulSingle

variable {I : Type*} [DecidableEq I] {M : I -> Type*}
variable [forall i, CommMonoid (M i)]

@[to_additive]
/--
theorem `Finset.univ_prod_mulSingle` / 定理 `Finset.univ_prod_mulSingle`

English:
theorem Finset.univ_prod_mulSingle
  given: [Fintype I] (f : forall i, M i)
  proof: by
  ext a
  simp

@[to_additive]

中文:
定理 有限集.univ_prod_mulSingle
  条件: [有限类型 I] (f : 对任意 i, M i)
  证明: by
  ext a
  simp

@[to_additive]
-/
theorem Finset.univ_prod_mulSingle [Fintype I] (f : forall i, M i) :
    (∏ i, Pi.mulSingle i (f i)) = f := by
  ext a
  simp

@[to_additive]
/--
theorem `MonoidHom.functions_ext` / 定理 `MonoidHom.functions_ext`

English:
theorem MonoidHom.functions_ext
  statement: [Finite I] (N : Type*) [CommMonoid N] (g h : (forall i, M i) ->* N)
  proof: by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k]; rw [map_prod]; rw [map_prod]
  simp only [H]

中文:
定理 幺半群态射.functions_ext
  结论: [有限 I] (N : 类型) [交换幺半群 N] (g h : (对任意 i, M i) ->* N)
  证明: by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k]; rw [map_prod]; rw [map_prod]
  simp only [H]

Depends on / 依赖: Finset, Finset.univ_prod_mulSingle, map_prod, nonempty_fintype, univ_prod_mulSingle
-/
theorem MonoidHom.functions_ext [Finite I] (N : Type*) [CommMonoid N] (g h : (forall i, M i) ->* N)
    (H : forall i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k]; rw [map_prod]; rw [map_prod]
  simp only [H]

/-- This is used as the ext lemma instead of `MonoidHom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext)
      /-- This is used as the ext lemma instead of `AddMonoidHom.functions_ext` for reasons
      explained in note [partially-applied ext lemmas]. -/]
/--
theorem `MonoidHom.functions_ext'` / 定理 `MonoidHom.functions_ext'`

English:
theorem MonoidHom.functions_ext'
  statement: [Finite I] (N : Type*) [CommMonoid N] (g h : (forall i, M i) ->* N)
  proof: g.functions_ext N h fun i => DFunLike.congr_fun (H i)

中文:
定理 幺半群态射.functions_ext'
  结论: [有限 I] (N : 类型) [交换幺半群 N] (g h : (对任意 i, M i) ->* N)
  证明: g.functions_ext N h fun i => DFunLike.congr_fun (H i)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, functions_ext, g.functions_ext
-/
theorem MonoidHom.functions_ext' [Finite I] (N : Type*) [CommMonoid N] (g h : (forall i, M i) ->* N)
    (H : forall i, g.comp (MonoidHom.mulSingle M i) = h.comp (MonoidHom.mulSingle M i)) : g = h :=
  g.functions_ext N h fun i => DFunLike.congr_fun (H i)

end MulSingle

section RingHom

open Pi

variable {I : Type*} [DecidableEq I] {R : I -> Type*}
variable [forall i, NonAssocSemiring (R i)]

@[ext]
/--
theorem `RingHom.functions_ext` / 定理 `RingHom.functions_ext`

English:
theorem RingHom.functions_ext
  statement: [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (forall i, R i) ->+* S)
  proof: RingHom.coe_addMonoidHom_injective
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (forall i, R i) ->+ S) h H

中文:
定理 环态射.functions_ext
  结论: [有限 I] (S : 类型) [非结合半环 S] (g h : (对任意 i, R i) ->+* S)
  证明: RingHom.coe_addMonoidHom_injective
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (forall i, R i) ->+ S) h H

Depends on / 依赖: AddMonoidHom, AddMonoidHom.functions_ext, RingHom, RingHom.coe_addMonoidHom_injective, coe_addMonoidHom_injective, functions_ext
-/
theorem RingHom.functions_ext [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (forall i, R i) ->+* S)
    (H : forall (i : I) (x : R i), g (single i x) = h (single i x)) : g = h :=
RingHom.coe_addMonoidHom_injective
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (forall i, R i) ->+ S) h H

end RingHom

namespace Prod

variable [CommMonoid M] [CommMonoid N] {s : Finset ι} {f : ι -> M × N}

@[to_additive]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  statement: (∏ c in s, f c).1 = ∏ c in s, (f c).1
  proof: map_prod (MonoidHom.fst ..) f s

@[to_additive]

中文:
定理 fst_prod
  结论: (∏ c in s, f c).1 = ∏ c in s, (f c).1
  证明: map_prod (MonoidHom.fst ..) f s

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.fst, map_prod
-/
theorem fst_prod : (∏ c in s, f c).1 = ∏ c in s, (f c).1 :=
  map_prod (MonoidHom.fst ..) f s

@[to_additive]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  statement: (∏ c in s, f c).2 = ∏ c in s, (f c).2
  proof: map_prod (MonoidHom.snd ..) f s

中文:
定理 snd_prod
  结论: (∏ c in s, f c).2 = ∏ c in s, (f c).2
  证明: map_prod (MonoidHom.snd ..) f s

Depends on / 依赖: MonoidHom, MonoidHom.snd, map_prod
-/
theorem snd_prod : (∏ c in s, f c).2 = ∏ c in s, (f c).2 :=
  map_prod (MonoidHom.snd ..) f s

end Prod

section MulEquiv

/-- The canonical isomorphism between the monoid of homomorphisms from a finite product of
commutative monoids to another commutative monoid and the product of the homomorphism monoids. -/
@[to_additive /-- The canonical isomorphism between the additive monoid of homomorphisms from
a finite product of additive commutative monoids to another additive commutative monoid and
the product of the homomorphism monoids. -/]
/--
Definition of `Pi.monoidHomMulEquiv` / `Pi.monoidHomMulEquiv` 的定义

English:
definition Pi.monoidHomMulEquiv
  signature: {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι -> Type*)
  body: φ.comp MonoidHom.mulSingle M i
  invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
  left_inv φ := by
    ext
    simp only [MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
      evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
refine congrArg _ funext fun _ =>

中文:
定义 依赖函数类型.monoidHomMulEquiv
  签名: {ι : 类型} [有限类型 ι] [DecidableEq ι] (M : ι -> 类型)
  定义体: φ.comp MonoidHom.mulSingle M i
  invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
  left_inv φ := by
    ext
    simp only [MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
      evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
refine congrArg _ funext fun _ =>

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, mulSingle
-/
def Pi.monoidHomMulEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι -> Type*)
    [(i : ι) -> CommMonoid (M i)] (M' : Type*) [CommMonoid M'] :
    (((i : ι) -> M i) ->* M') ≃* ((i : ι) -> (M i ->* M')) where
toFun φ i := φ.comp MonoidHom.mulSingle M i
  invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
  left_inv φ := by
    ext
    simp only [MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
      evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
refine congrArg _ funext fun _ => ?_
    rw [Fintype.prod_apply]
    exact Fintype.prod_pi_mulSingle ..
  right_inv φ := by
    ext i m
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
      MonoidHom.finsetProd_apply, evalMonoidHom_apply, ]
    let φ' i : M i -> M' := ⇑(φ i)
    conv =>
      enter [1, 2, j]
      rw [show φ j = φ' j from rfl]; rw [Pi.apply_mulSingle φ' (fun i => map_one (φ i))]
    rw [show φ' i = φ i from rfl]
    exact Fintype.prod_pi_mulSingle' ..
  map_mul' φ ψ := by
    ext
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
      MonoidHom.mul_apply, mul_apply]

end MulEquiv

variable [Finite ι] [DecidableEq ι] {M : ι -> Type*}

-- manually additivized to fix variable names
-- See https://github.com/leanprover-community/mathlib4/issues/11462
/--
lemma `Pi.single_induction` / 引理 `Pi.single_induction`

English:
lemma Pi.single_induction
  statement: [forall i, AddCommMonoid (M i)] (p : (Π i, M i) -> Prop) (f : Π i, M i)
  proof: by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

@[to_additive existing (attr := elab_as_elim)]

中文:
引理 依赖函数类型.single_induction
  结论: [对任意 i, 加法交换幺半群 (M i)] (p : (Π i, M i) -> 命题) (f : Π i, M i)
  证明: by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

@[to_additive existing (attr := elab_as_elim)]

Depends on / 依赖: Finset, Finset.sum_induction, Finset.univ_sum_single, nonempty_fintype, single, sum_induction, univ_sum_single
-/
lemma Pi.single_induction [forall i, AddCommMonoid (M i)] (p : (Π i, M i) -> Prop) (f : Π i, M i)
    (zero : p 0) (add : forall f g, p f -> p g -> p (f + g))
    (single : forall i m, p (Pi.single i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

@[to_additive existing (attr := elab_as_elim)]
/--
lemma `Pi.mulSingle_induction` / 引理 `Pi.mulSingle_induction`

English:
lemma Pi.mulSingle_induction
  statement: [forall i, CommMonoid (M i)] (p : (Π i, M i) -> Prop) (f : Π i, M i)
  proof: by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

中文:
引理 依赖函数类型.mulSingle_induction
  结论: [对任意 i, 交换幺半群 (M i)] (p : (Π i, M i) -> 命题) (f : Π i, M i)
  证明: by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

Depends on / 依赖: Finset, Finset.prod_induction, Finset.univ_prod_mulSingle, mulSingle, nonempty_fintype, prod_induction, univ_prod_mulSingle
-/
lemma Pi.mulSingle_induction [forall i, CommMonoid (M i)] (p : (Π i, M i) -> Prop) (f : Π i, M i)
    (one : p 1) (mul : forall f g, p f -> p g -> p (f * g))
    (mulSingle : forall i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

section EqOn

@[to_additive]
/--
theorem `eqOn_finsetProd` / 定理 `eqOn_finsetProd`

English:
theorem eqOn_finsetProd
  statement: {ι α β : Type*} [CommMonoid α]
  proof: fun t ht => by simp [funext fun i => h i ht]

@[to_additive]

中文:
定理 eqOn_finsetProd
  结论: {ι α β : 类型} [交换幺半群 α]
  证明: fun t ht => by simp [funext fun i => h i ht]

@[to_additive]
-/
theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι -> β -> α} (h : forall (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (∏ i in v, f i) (∏ i in v, f' i) s :=
  fun t ht => by simp [funext fun i => h i ht]

@[to_additive]
/--
theorem `eqOn_fun_finsetProd` / 定理 `eqOn_fun_finsetProd`

English:
theorem eqOn_fun_finsetProd
  statement: {ι α β : Type*} [CommMonoid α]
  proof: by
  convert! eqOn_finsetProd h v <;> simp

中文:
定理 eqOn_fun_finsetProd
  结论: {ι α β : 类型} [交换幺半群 α]
  证明: by
  convert! eqOn_finsetProd h v <;> simp

Depends on / 依赖: convert, eqOn_finsetProd
-/
theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι -> β -> α} (h : forall (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (fun b => ∏ i in v, f i b) (fun b => ∏ i in v, f' i b) s := by
  convert! eqOn_finsetProd h v <;> simp

end EqOn

section FunLike

variable {F α β ι : Type*} [FunLike F α β] [CommMonoid β] [CommMonoid F]
  [IsOneApply F α β] [IsMulApply F α β]

@[to_additive (attr := simp, grind =)]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (s : Finset ι) (f : ι -> F) (x : α)
  statement: (∏ i in s, f i) x = ∏ i in s, f i x
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h => simp [his, h]

@[to_additive (attr := norm_cast)]

中文:
定理 prod_apply
  条件: (s : 有限集 ι) (f : ι -> F) (x : α)
  结论: (∏ i in s, f i) x = ∏ i in s, f i x
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h => simp [his, h]

@[to_additive (attr := norm_cast)]

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on, insert
-/
theorem prod_apply (s : Finset ι) (f : ι -> F) (x : α) : (∏ i in s, f i) x = ∏ i in s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h => simp [his, h]

@[to_additive (attr := norm_cast)]
/--
theorem `FunLike.coe_prod` / 定理 `FunLike.coe_prod`

English:
theorem FunLike.coe_prod
  given: (s : Finset ι) (f : ι -> F)
  statement: ↑(∏ i in s, f i) = ∏ i in s, (f i : α -> β)
  proof: by
  ext; simp

中文:
定理 函数状.coe_prod
  条件: (s : 有限集 ι) (f : ι -> F)
  结论: ↑(∏ i in s, f i) = ∏ i in s, (f i : α -> β)
  证明: by
  ext; simp
-/
theorem FunLike.coe_prod (s : Finset ι) (f : ι -> F) : ↑(∏ i in s, f i) = ∏ i in s, (f i : α -> β) := by
  ext; simp

end FunLike
