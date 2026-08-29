/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Logic.Small.Basic

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.mk`: a function sending an element of `M` to `M ⧸ p`
* `Submodule.Quotient.module`: `M ⧸ p` is a module
* `Submodule.Quotient.mkQ`: a linear map sending an element of `M` to `M ⧸ p`
* `Submodule.quotEquivOfEq`: if `p` and `p'` are equal, their quotients are equivalent

-/

@[expose] public section

-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)

open QuotientAddGroup

/--
Definition of `quotientRel` / `quotientRel` 的定义

English:
definition quotientRel
  signature: : Setoid M
  body: QuotientAddGroup.leftRel p.toAddSubgroup

中文:
定义 quotientRel
  签名: : 集合等价关系 M
  定义体: QuotientAddGroup.leftRel p.toAddSubgroup

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.leftRel, leftRel, p.toAddSubgroup, toAddSubgroup
-/
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

/--
theorem `quotientRel_def` / 定理 `quotientRel_def`

English:
theorem quotientRel_def
  given: {x y : M}
  statement: p.quotientRel x y ↔ x - y in p
  proof: Iff.trans
    (by
      rw [quotientRel]; rw [leftRel_apply]; rw [sub_eq_add_neg]; rw [neg_add]; rw [neg_neg]
      rfl)
    neg_mem_iff

中文:
定理 quotientRel_def
  条件: {x y : M}
  结论: p.quotientRel x y ↔ x - y in p
  证明: Iff.trans
    (by
      rw [quotientRel]; rw [leftRel_apply]; rw [sub_eq_add_neg]; rw [neg_add]; rw [neg_neg]
      rfl)
    neg_mem_iff

Depends on / 依赖: Iff.trans, MeasurableSet, Set.inter_subset_left, Set.inter_subset_right, Set.subset_inter, hs_subset, hs_subset_t, ht.inter, iInf_eq_top, inter_subset_left, inter_subset_right, leftRel_apply, measurableSet_sigmaFiniteSetWRT, measure_eq_iInf, measure_mono_top, neg_add, neg_mem_iff, neg_neg, quotientRel, sigmaFiniteSetWRT
-/
theorem quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y in p :=
  Iff.trans
    (by
      rw [quotientRel]; rw [leftRel_apply]; rw [sub_eq_add_neg]; rw [neg_add]; rw [neg_neg]
      rfl)
    neg_mem_iff

/--
Instance `hasQuotient` / 实例 `hasQuotient`

English:
instance hasQuotient
  signature: : HasQuotient M (Submodule R M)
  body: ⟨fun p => Quotient (quotientRel p)⟩

中文:
实例 hasQuotient
  签名: : 有商 M (子模 R M)
  定义体: ⟨fun p => Quotient (quotientRel p)⟩

Depends on / 依赖: Quotient, quotientRel
-/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

namespace Quotient
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {p : Submodule R M}
  body: Quotient.mk''

中文:
定义 mk
  签名: {p : 子模 R M}
  定义体: Quotient.mk''

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk {p : Submodule R M} : M -> M ⧸ p :=
  Quotient.mk''

/--
theorem `mk'_eq_mk'` / 定理 `mk'_eq_mk'`

English:
theorem mk'_eq_mk'
  given: {p : Submodule R M} (x : M)
  proof: rfl

中文:
定理 mk'_eq_mk'
  条件: {p : 子模 R M} (x : M)
  证明: rfl
-/
theorem mk'_eq_mk' {p : Submodule R M} (x : M) :
    @Quotient.mk' _ (quotientRel p) x = mk x :=
  rfl

/--
theorem `mk''_eq_mk` / 定理 `mk''_eq_mk`

English:
theorem mk''_eq_mk
  given: {p : Submodule R M} (x : M)
  statement: (Quotient.mk'' x : M ⧸ p) = mk x
  proof: rfl

中文:
定理 mk''_eq_mk
  条件: {p : 子模 R M} (x : M)
  结论: (商.mk'' x : M ⧸ p) = mk x
  证明: rfl
-/
theorem mk''_eq_mk {p : Submodule R M} (x : M) : (Quotient.mk'' x : M ⧸ p) = mk x :=
  rfl

/--
theorem `quot_mk_eq_mk` / 定理 `quot_mk_eq_mk`

English:
theorem quot_mk_eq_mk
  given: {p : Submodule R M} (x : M)
  statement: (Quot.mk _ x : M ⧸ p) = mk x
  proof: rfl

中文:
定理 quot_mk_eq_mk
  条件: {p : 子模 R M} (x : M)
  结论: (商.mk _ x : M ⧸ p) = mk x
  证明: rfl
-/
theorem quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = mk x :=
  rfl

/--
theorem `quotientAddGroupMk_eq_mk` / 定理 `quotientAddGroupMk_eq_mk`

English:
theorem quotientAddGroupMk_eq_mk
  given: {p : Submodule R M} (x : M)
  proof: rfl

中文:
定理 quotientAddGroupMk_eq_mk
  条件: {p : 子模 R M} (x : M)
  证明: rfl
-/
theorem quotientAddGroupMk_eq_mk {p : Submodule R M} (x : M) :
    (QuotientAddGroup.mk x : M ⧸ p) = mk x :=
  rfl

/--
theorem `eq'` / 定理 `eq'`

English:
theorem eq'
  given: {x y : M}
  statement: (mk x : M ⧸ p) = mk y ↔ -x + y in p
  proof: QuotientAddGroup.eq

中文:
定理 eq'
  条件: {x y : M}
  结论: (mk x : M ⧸ p) = mk y ↔ -x + y in p
  证明: QuotientAddGroup.eq
-/
protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y in p :=
  QuotientAddGroup.eq

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {x y : M}
  statement: (mk x : M ⧸ p) = mk y ↔ x - y in p
  proof: (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)

中文:
定理 eq
  条件: {x y : M}
  结论: (mk x : M ⧸ p) = mk y ↔ x - y in p
  证明: (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)
-/
protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y in p :=
  (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ⧸ p)
  body: Quotient.mk'' 0

中文:
实例 :
  签名: 零 (M ⧸ p)
  定义体: Quotient.mk'' 0

Depends on / 依赖: Quotient, Quotient.mk
-/
instance : Zero (M ⧸ p) where
  -- Use Quotient.mk'' instead of mk here because mk is not reducible.
  -- This would lead to non-defeq diamonds.
  -- See also the same comment at the One instance for Con.
  zero := Quotient.mk'' 0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ⧸ p)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 (M ⧸ p)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (M ⧸ p) :=
  ⟨0⟩

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: mk 0 = (0 : M ⧸ p)
  proof: rfl

@[simp]

中文:
定理 mk_zero
  结论: mk 0 = (0 : M ⧸ p)
  证明: rfl

@[simp]
-/
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  statement: (mk x : M ⧸ p) = 0 ↔ x in p
  proof: by simpa using (Quotient.eq' p : mk x = 0 ↔ _)

中文:
定理 mk_eq_zero
  结论: (mk x : M ⧸ p) = 0 ↔ x in p
  证明: by simpa using (Quotient.eq' p : mk x = 0 ↔ _)

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p := by simpa using (Quotient.eq' p : mk x = 0 ↔ _)

section SMul

variable {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] (P : Submodule R M)

/--
Instance `instSMul'` / 实例 `instSMul'`

English:
instance instSMul'
  signature: : SMul S (M ⧸ P)
  body: ⟨fun a =>
    Quotient.map' (a • ·) fun x y h =>
leftRel_apply.mpr by simpa using Submodule.smul_mem P (a • (1 : R)) (leftRel_apply.mp h)⟩

中文:
实例 instSMul'
  签名: : 标量乘法 S (M ⧸ P)
  定义体: ⟨fun a =>
    Quotient.map' (a • ·) fun x y h =>
leftRel_apply.mpr by simpa using Submodule.smul_mem P (a • (1 : R)) (leftRel_apply.mp h)⟩

Depends on / 依赖: Quotient, Quotient.map, Submodule, Submodule.smul_mem, leftRel_apply, leftRel_apply.mp, leftRel_apply.mpr, smul_mem
-/
instance instSMul' : SMul S (M ⧸ P) :=
  ⟨fun a =>
    Quotient.map' (a • ·) fun x y h =>
leftRel_apply.mpr by simpa using Submodule.smul_mem P (a • (1 : R)) (leftRel_apply.mp h)⟩

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul R (M ⧸ P)
  body: Quotient.instSMul' P

@[simp]

中文:
实例 instSMul
  签名: : 标量乘法 R (M ⧸ P)
  定义体: Quotient.instSMul' P

@[simp]

Depends on / 依赖: Quotient, Quotient.instSMul, instSMul
-/
instance instSMul : SMul R (M ⧸ P) :=
  Quotient.instSMul' P

@[simp]
/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: (r : S) (x : M)
  statement: (mk (r • x) : M ⧸ p) = r • mk x
  proof: rfl

中文:
定理 mk_smul
  条件: (r : S) (x : M)
  结论: (mk (r • x) : M ⧸ p) = r • mk x
  证明: rfl
-/
theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x :=
  rfl

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M]
  body: Quotient.ind' fun _z => congr_arg mk (smul_comm _ _ _)

中文:
实例 smulCommClass
  签名: (T : 类型) [标量乘法 T R] [标量乘法 T M] [标量塔 T R M]
  定义体: Quotient.ind' fun _z => congr_arg mk (smul_comm _ _ _)

Depends on / 依赖: Quotient, Quotient.ind, congr_arg, smul_comm
-/
instance smulCommClass (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M]
    [SMulCommClass S T M] : SMulCommClass S T (M ⧸ P) where
  smul_comm _x _y := Quotient.ind' fun _z => congr_arg mk (smul_comm _ _ _)

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMul S T]
  body: Quotient.ind' fun _z => congr_arg mk (smul_assoc _ _ _)

中文:
实例 isScalarTower
  签名: (T : 类型) [标量乘法 T R] [标量乘法 T M] [标量塔 T R M] [标量乘法 S T]
  定义体: Quotient.ind' fun _z => congr_arg mk (smul_assoc _ _ _)

Depends on / 依赖: Quotient, Quotient.ind, congr_arg, smul_assoc
-/
instance isScalarTower (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMul S T]
    [IsScalarTower S T M] : IsScalarTower S T (M ⧸ P) where
  smul_assoc _x _y := Quotient.ind' fun _z => congr_arg mk (smul_assoc _ _ _)

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
  body: Quotient.ind' fun _z => congr_arg mk op_smul_eq_smul _ _

中文:
实例 isCentralScalar
  签名: [标量乘法 Sᵐᵒᵖ R] [标量乘法 Sᵐᵒᵖ M] [标量塔 Sᵐᵒᵖ R M]
  定义体: Quotient.ind' fun _z => congr_arg mk op_smul_eq_smul _ _

Depends on / 依赖: Quotient, Quotient.ind, congr_arg, op_smul_eq_smul
-/
instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] : IsCentralScalar S (M ⧸ P) where
op_smul_eq_smul _x := Quotient.ind' fun _z => congr_arg mk op_smul_eq_smul _ _

end SMul

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid (M ⧸ p)
  body: inferInstanceAs AddMonoid (M ⧸ p.toAddSubgroup)

中文:
实例 addMonoid
  签名: : 加法幺半群 (M ⧸ p)
  定义体: inferInstanceAs AddMonoid (M ⧸ p.toAddSubgroup)

Depends on / 依赖: AddMonoid, p.toAddSubgroup, toAddSubgroup
-/
instance addMonoid : AddMonoid (M ⧸ p) :=
inferInstanceAs AddMonoid (M ⧸ p.toAddSubgroup)

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (M ⧸ p)
  body: inferInstanceAs AddCommMonoid (M ⧸ p.toAddSubgroup)

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (M ⧸ p)
  定义体: inferInstanceAs AddCommMonoid (M ⧸ p.toAddSubgroup)

Depends on / 依赖: AddCommMonoid, p.toAddSubgroup, toAddSubgroup
-/
instance addCommMonoid : AddCommMonoid (M ⧸ p) :=
inferInstanceAs AddCommMonoid (M ⧸ p.toAddSubgroup)

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup (M ⧸ p)
  body: inferInstanceAs AddCommGroup (M ⧸ p.toAddSubgroup)

@[simp]

中文:
实例 addCommGroup
  签名: : 加法交换群 (M ⧸ p)
  定义体: inferInstanceAs AddCommGroup (M ⧸ p.toAddSubgroup)

@[simp]

Depends on / 依赖: AddCommGroup, p.toAddSubgroup, toAddSubgroup
-/
instance addCommGroup : AddCommGroup (M ⧸ p) :=
inferInstanceAs AddCommGroup (M ⧸ p.toAddSubgroup)

@[simp]
/--
theorem `mk_add` / 定理 `mk_add`

English:
theorem mk_add
  statement: (mk (x + y) : M ⧸ p) = mk x + mk y
  proof: rfl

@[simp]

中文:
定理 mk_add
  结论: (mk (x + y) : M ⧸ p) = mk x + mk y
  证明: rfl

@[simp]
-/
theorem mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y :=
  rfl

@[simp]
/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  statement: (mk (-x) : M ⧸ p) = -(mk x)
  proof: rfl

@[simp]

中文:
定理 mk_neg
  结论: (mk (-x) : M ⧸ p) = -(mk x)
  证明: rfl

@[simp]
-/
theorem mk_neg : (mk (-x) : M ⧸ p) = -(mk x) :=
  rfl

@[simp]
/--
theorem `mk_sub` / 定理 `mk_sub`

English:
theorem mk_sub
  statement: (mk (x - y) : M ⧸ p) = mk x - mk y
  proof: rfl

中文:
定理 mk_sub
  结论: (mk (x - y) : M ⧸ p) = mk x - mk y
  证明: rfl
-/
theorem mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y :=
  rfl

variable {p} in
@[simp]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  given: (m : M ⧸ p)
  statement: Submodule.Quotient.mk (Quotient.out m) = m
  proof: Quotient.out_eq m

protected nonrec lemma «forall» {P : M ⧸ p -> Prop} : (forall a, P a) ↔ forall a, P (mk a) := Quotient.forall

中文:
定理 mk_out
  条件: (m : M ⧸ p)
  结论: 子模.商.mk (商.out m) = m
  证明: Quotient.out_eq m

protected nonrec lemma «forall» {P : M ⧸ p -> Prop} : (forall a, P a) ↔ forall a, P (mk a) := Quotient.forall

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem mk_out (m : M ⧸ p) : Submodule.Quotient.mk (Quotient.out m) = m :=
  Quotient.out_eq m

protected nonrec lemma «forall» {P : M ⧸ p -> Prop} : (forall a, P a) ↔ forall a, P (mk a) := Quotient.forall

section Module

variable {S : Type*}

/--
Instance `mulAction'` / 实例 `mulAction'`

English:
instance mulAction'
  signature: [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
  body: fast_instance%
Function.Surjective.mulAction mk Quot.mk_surjective Submodule.Quotient.mk_smul P

中文:
实例 mulAction'
  签名: [幺半群 S] [标量乘法 S R] [乘法作用 S M] [标量塔 S R M]
  定义体: fast_instance%
Function.Surjective.mulAction mk Quot.mk_surjective Submodule.Quotient.mk_smul P

Depends on / 依赖: fast_instance
-/
instance mulAction' [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : MulAction S (M ⧸ P) := fast_instance%
Function.Surjective.mulAction mk Quot.mk_surjective Submodule.Quotient.mk_smul P

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: (P : Submodule R M)
  body: Quotient.mulAction' P

中文:
实例 mulAction
  签名: (P : 子模 R M)
  定义体: Quotient.mulAction' P

Depends on / 依赖: Quotient, Quotient.mulAction, mulAction
-/
instance mulAction (P : Submodule R M) : MulAction R (M ⧸ P) :=
  Quotient.mulAction' P

/--
Instance `smulZeroClass'` / 实例 `smulZeroClass'`

English:
instance smulZeroClass'
  signature: [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : Submodule R M)
  body: ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ Submodule.Quotient.mk_smul P

中文:
实例 smulZeroClass'
  签名: [标量乘法 S R] [SMulZero类 S M] [标量塔 S R M] (P : 子模 R M)
  定义体: ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ Submodule.Quotient.mk_smul P

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_smul, ZeroHom, ZeroHom.smulZeroClass, mk_smul, mk_zero, smulZeroClass
-/
instance smulZeroClass' [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : Submodule R M) :
    SMulZeroClass S (M ⧸ P) :=
ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ Submodule.Quotient.mk_smul P

/--
Instance `smulZeroClass` / 实例 `smulZeroClass`

English:
instance smulZeroClass
  signature: (P : Submodule R M)
  body: Quotient.smulZeroClass' P

中文:
实例 smulZeroClass
  签名: (P : 子模 R M)
  定义体: Quotient.smulZeroClass' P

Depends on / 依赖: Quotient, Quotient.smulZeroClass, smulZeroClass
-/
instance smulZeroClass (P : Submodule R M) : SMulZeroClass R (M ⧸ P) :=
  Quotient.smulZeroClass' P

/--
Instance `distribSMul'` / 实例 `distribSMul'`

English:
instance distribSMul'
  signature: [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submodule R M)
  body: fast_instance%
  Function.Surjective.distribSMul { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

中文:
实例 distribSMul'
  签名: [标量乘法 S R] [分配标量乘法 S M] [标量塔 S R M] (P : 子模 R M)
  定义体: fast_instance%
  Function.Surjective.distribSMul { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

Depends on / 依赖: fast_instance
-/
instance distribSMul' [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submodule R M) :
    DistribSMul S (M ⧸ P) := fast_instance%
  Function.Surjective.distribSMul { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

/--
Instance `distribSMul` / 实例 `distribSMul`

English:
instance distribSMul
  signature: (P : Submodule R M)
  body: Quotient.distribSMul' P

中文:
实例 distribSMul
  签名: (P : 子模 R M)
  定义体: Quotient.distribSMul' P

Depends on / 依赖: Quotient, Quotient.distribSMul, distribSMul
-/
instance distribSMul (P : Submodule R M) : DistribSMul R (M ⧸ P) :=
  Quotient.distribSMul' P

/--
Instance `distribMulAction'` / 实例 `distribMulAction'`

English:
instance distribMulAction'
  signature: [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTower S R M]
  body: fast_instance%
  Function.Surjective.distribMulAction { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

中文:
实例 distribMulAction'
  签名: [幺半群 S] [标量乘法 S R] [分配乘法作用 S M] [标量塔 S R M]
  定义体: fast_instance%
  Function.Surjective.distribMulAction { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

Depends on / 依赖: fast_instance
-/
instance distribMulAction' [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : DistribMulAction S (M ⧸ P) := fast_instance%
  Function.Surjective.distribMulAction { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: (P : Submodule R M)
  body: Quotient.distribMulAction' P

中文:
实例 distribMulAction
  签名: (P : 子模 R M)
  定义体: Quotient.distribMulAction' P

Depends on / 依赖: Quotient, Quotient.distribMulAction, distribMulAction
-/
instance distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P) :=
  Quotient.distribMulAction' P

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M)
  body: fast_instance%
  Function.Surjective.module _ { toFun := mk, map_zero' := by rfl, map_add' := fun _ _ => by rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

中文:
实例 module'
  签名: [半环 S] [标量乘法 S R] [模 S M] [标量塔 S R M] (P : 子模 R M)
  定义体: fast_instance%
  Function.Surjective.module _ { toFun := mk, map_zero' := by rfl, map_add' := fun _ _ => by rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

Depends on / 依赖: fast_instance
-/
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    Module S (M ⧸ P) := fast_instance%
  Function.Surjective.module _ { toFun := mk, map_zero' := by rfl, map_add' := fun _ _ => by rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: (P : Submodule R M)
  body: Quotient.module' P

中文:
实例 module
  签名: (P : 子模 R M)
  定义体: Quotient.module' P

Depends on / 依赖: Quotient, Quotient.module, module
-/
instance module (P : Submodule R M) : Module R (M ⧸ P) :=
  Quotient.module' P

end Module

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {C : M ⧸ p -> Prop} (x : M ⧸ p) (H : forall z, C (Submodule.Quotient.mk z))
  proof: Quotient.inductionOn' x H

中文:
定理 induction_on
  条件: {C : M ⧸ p -> 命题} (x : M ⧸ p) (H : 对任意 z, C (子模.商.mk z))
  证明: Quotient.inductionOn' x H

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem induction_on {C : M ⧸ p -> Prop} (x : M ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) :
    C x := Quotient.inductionOn' x H

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (@mk _ _ _ _ _ p)
  proof: by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

universe u in

中文:
定理 mk_surjective
  结论: 函数.满射 (@mk _ _ _ _ _ p)
  证明: by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

universe u in
-/
theorem mk_surjective : Function.Surjective (@mk _ _ _ _ _ p) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

universe u in
instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {N : Submodule R M} [Small.{u} M] :
    Small.{u} (M ⧸ N) :=
  small_of_surjective (Submodule.Quotient.mk_surjective _)

end Quotient

section

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

/--
theorem `quot_hom_ext` / 定理 `quot_hom_ext`

English:
theorem quot_hom_ext
  given: (f g : (M ⧸ p) ->ₗ[R] M₂) (h : forall x : M, f (Quotient.mk x) = g (Quotient.mk x))
  proof: LinearMap.ext fun x => Submodule.Quotient.induction_on _ x h

中文:
定理 quot_hom_ext
  条件: (f g : (M ⧸ p) ->ₗ[R] M₂) (h : 对任意 x : M, f (商.mk x) = g (商.mk x))
  证明: LinearMap.ext fun x => Submodule.Quotient.induction_on _ x h

Depends on / 依赖: LinearMap, LinearMap.ext, Quotient, Submodule, Submodule.Quotient.induction_on, induction_on
-/
theorem quot_hom_ext (f g : (M ⧸ p) ->ₗ[R] M₂) (h : forall x : M, f (Quotient.mk x) = g (Quotient.mk x)) :
    f = g :=
  LinearMap.ext fun x => Submodule.Quotient.induction_on _ x h

/--
Definition of `mkQ` / `mkQ` 的定义

English:
definition mkQ
  signature: : M ->ₗ[R] M ⧸ p where
  body: Quotient.mk
  map_add' := by simp
  map_smul' := by simp

@[simp]

中文:
定义 mkQ
  签名: : M ->ₗ[R] M ⧸ p where
  定义体: Quotient.mk
  map_add' := by simp
  map_smul' := by simp

@[simp]

Depends on / 依赖: Quotient, Quotient.mk
-/
def mkQ : M ->ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp

@[simp]
/--
theorem `mkQ_apply` / 定理 `mkQ_apply`

English:
theorem mkQ_apply
  given: (x : M)
  statement: p.mkQ x = Quotient.mk x
  proof: rfl

中文:
定理 mkQ_apply
  条件: (x : M)
  结论: p.mkQ x = 商.mk x
  证明: rfl
-/
theorem mkQ_apply (x : M) : p.mkQ x = Quotient.mk x :=
  rfl

/--
theorem `mkQ_surjective` / 定理 `mkQ_surjective`

English:
theorem mkQ_surjective
  statement: Function.Surjective p.mkQ
  proof: by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

中文:
定理 mkQ_surjective
  结论: 函数.满射 p.mkQ
  证明: by
  rintro ⟨x⟩; exact ⟨x, rfl⟩
-/
theorem mkQ_surjective : Function.Surjective p.mkQ := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

end

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R ->+* R₂}

/-- Two `LinearMap`s from a quotient module are equal if their compositions with
`submodule.mkQ` are equal.

See note [partially-applied ext lemmas]. -/
@[ext high] -- Increase priority so this applies before `LinearMap.ext`
/--
theorem `linearMap_qext` / 定理 `linearMap_qext`

English:
theorem linearMap_qext
  given: ⦃f g
  statement: M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g
  proof: LinearMap.ext fun x => Submodule.Quotient.induction_on _ x (LinearMap.congr_fun h :)

中文:
定理 linearMap_qext
  条件: ⦃f g
  结论: M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g
  证明: LinearMap.ext fun x => Submodule.Quotient.induction_on _ x (LinearMap.congr_fun h :)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, LinearMap.ext, Quotient, Submodule, Submodule.Quotient.induction_on, congr_fun, induction_on
-/
theorem linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g :=
LinearMap.ext fun x => Submodule.Quotient.induction_on _ x (LinearMap.congr_fun h :)

/--
Definition of `quotEquivOfEq` / `quotEquivOfEq` 的定义

English:
definition quotEquivOfEq
  signature: (h : p = p')
  body: { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }

@[simp]

中文:
定义 quotEquivOfEq
  签名: (h : p = p')
  定义体: { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }

@[simp]

Depends on / 依赖: Equiv.refl, Quotient, Quotient.congr, map_add, map_smul, quotientRel
-/
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }

@[simp]
/--
theorem `quotEquivOfEq_mk` / 定理 `quotEquivOfEq_mk`

English:
theorem quotEquivOfEq_mk
  given: (h : p = p') (x : M)
  proof: rfl

中文:
定理 quotEquivOfEq_mk
  条件: (h : p = p') (x : M)
  证明: rfl
-/
theorem quotEquivOfEq_mk (h : p = p') (x : M) :
    Submodule.quotEquivOfEq p p' h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x) :=
  rfl

end Submodule

end Ring
