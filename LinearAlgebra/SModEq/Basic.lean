/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# modular equivalence for submodule
-/

@[expose] public section


open Submodule

open Polynomial

variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] (U U₁ U₂ : Submodule R M)
variable {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}
variable {N : Type*} [AddCommGroup N] [Module R N] (V V₁ V₂ : Submodule R N)

/--
Definition of `SModEq` / `SModEq` 的定义

English:
definition SModEq
  signature: (x y : M)
  body: (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y

@[inherit_doc] notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

中文:
定义 SModEq
  签名: (x y : M)
  定义体: (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y

@[inherit_doc] notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk
-/
def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y

@[inherit_doc] notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

variable {U U₁ U₂}

/--
theorem `SModEq.def` / 定理 `SModEq.def`

English:
theorem SModEq.def
  proof: Iff.rfl

中文:
定理 SModEq.def
  证明: Iff.rfl
-/
protected theorem SModEq.def :
    x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl

namespace SModEq

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  statement: x ≡ y [SMOD U] ↔ x - y in U
  proof: by rw [SModEq.def, Submodule.Quotient.eq]

@[simp]

中文:
定理 sub_mem
  结论: x ≡ y [SMOD U] ↔ x - y in U
  证明: by rw [SModEq.def, Submodule.Quotient.eq]

@[simp]

Depends on / 依赖: Quotient, SModEq, SModEq.def, Submodule, Submodule.Quotient.eq
-/
theorem sub_mem : x ≡ y [SMOD U] ↔ x - y in U := by rw [SModEq.def, Submodule.Quotient.eq]

@[simp]
/--
theorem `top` / 定理 `top`

English:
theorem top
  statement: x ≡ y [SMOD (⊤ : Submodule R M)]
  proof: (Submodule.Quotient.eq ⊤).2 mem_top

@[simp]

中文:
定理 top
  结论: x ≡ y [SMOD (⊤ : 子模 R M)]
  证明: (Submodule.Quotient.eq ⊤).2 mem_top

@[simp]

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.eq, mem_top
-/
theorem top : x ≡ y [SMOD (⊤ : Submodule R M)] :=
  (Submodule.Quotient.eq ⊤).2 mem_top

@[simp]
/--
theorem `bot` / 定理 `bot`

English:
theorem bot
  statement: x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y
  proof: by
  rw [SModEq.def]; rw [Submodule.Quotient.eq]; rw [mem_bot]; rw [sub_eq_zero]

@[gcongr, mono]

中文:
定理 bot
  结论: x ≡ y [SMOD (⊥ : 子模 R M)] ↔ x = y
  证明: by
  rw [SModEq.def]; rw [Submodule.Quotient.eq]; rw [mem_bot]; rw [sub_eq_zero]

@[gcongr, mono]

Depends on / 依赖: Quotient, SModEq, SModEq.def, Submodule, Submodule.Quotient.eq, mem_bot, sub_eq_zero
-/
theorem bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y := by
  rw [SModEq.def]; rw [Submodule.Quotient.eq]; rw [mem_bot]; rw [sub_eq_zero]

@[gcongr, mono]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁])
  statement: x ≡ y [SMOD U₂]
  proof: (Submodule.Quotient.eq U₂).2 HU (Submodule.Quotient.eq U₁).1 hxy

中文:
定理 mono
  条件: (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁])
  结论: x ≡ y [SMOD U₂]
  证明: (Submodule.Quotient.eq U₂).2 HU (Submodule.Quotient.eq U₁).1 hxy

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.eq
-/
theorem mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
(Submodule.Quotient.eq U₂).2 HU (Submodule.Quotient.eq U₁).1 hxy

/--
lemma `of_toAddSubgroup_le` / 引理 `of_toAddSubgroup_le`

English:
lemma of_toAddSubgroup_le
  statement: {U : Submodule R M} {V : Submodule S M}
  proof: by
  simp only [SModEq, Submodule.Quotient.eq] at hxy ⊢
  exact h hxy

@[refl, simp]

中文:
引理 of_toAddSubgroup_le
  结论: {U : 子模 R M} {V : 子模 S M}
  证明: by
  simp only [SModEq, Submodule.Quotient.eq] at hxy ⊢
  exact h hxy

@[refl, simp]

Depends on / 依赖: Quotient, SModEq, Submodule, Submodule.Quotient.eq
-/
lemma of_toAddSubgroup_le {U : Submodule R M} {V : Submodule S M}
    (h : U.toAddSubgroup <= V.toAddSubgroup) {x y : M} (hxy : x ≡ y [SMOD U]) : x ≡ y [SMOD V] := by
  simp only [SModEq, Submodule.Quotient.eq] at hxy ⊢
  exact h hxy

@[refl, simp]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (x : M)
  statement: x ≡ x [SMOD U]
  proof: @rfl _ _

中文:
定理 refl
  条件: (x : M)
  结论: x ≡ x [SMOD U]
  证明: @rfl _ _
-/
protected theorem refl (x : M) : x ≡ x [SMOD U] :=
  @rfl _ _

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  statement: x ≡ x [SMOD U]
  proof: SModEq.refl _

中文:
定理 rfl
  结论: x ≡ x [SMOD U]
  证明: SModEq.refl _
-/
protected theorem rfl : x ≡ x [SMOD U] :=
  SModEq.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Refl (SModEq U)
  body: ⟨SModEq.refl⟩

@[symm]
nonrec theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm

中文:
实例 :
  签名: Std.Refl (SModEq U)
  定义体: ⟨SModEq.refl⟩

@[symm]
nonrec theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm

Depends on / 依赖: SModEq, SModEq.refl
-/
instance : Std.Refl (SModEq U) :=
  ⟨SModEq.refl⟩

@[symm]
nonrec theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  statement: x ≡ y [SMOD U] ↔ y ≡ x [SMOD U]
  proof: ⟨symm, symm⟩

@[trans]
nonrec theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz

中文:
定理 comm
  结论: x ≡ y [SMOD U] ↔ y ≡ x [SMOD U]
  证明: ⟨symm, symm⟩

@[trans]
nonrec theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz
-/
theorem comm : x ≡ y [SMOD U] ↔ y ≡ x [SMOD U] := ⟨symm, symm⟩

@[trans]
nonrec theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz

/--
Instance `instTrans` / 实例 `instTrans`

English:
instance instTrans
  signature: : Trans (SModEq U) (SModEq U) (SModEq U) where
  body: trans

@[gcongr]

中文:
实例 instTrans
  签名: : Trans (SModEq U) (SModEq U) (SModEq U) where
  定义体: trans

@[gcongr]
-/
instance instTrans : Trans (SModEq U) (SModEq U) (SModEq U) where
  trans := trans

@[gcongr]
/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U])
  statement: x₁ + x₂ ≡ y₁ + y₂ [SMOD U]
  proof: by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_add, hxy₁, hxy₂]

@[gcongr]

中文:
定理 add
  条件: (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U])
  结论: x₁ + x₂ ≡ y₁ + y₂ [SMOD U]
  证明: by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_add, hxy₁, hxy₂]

@[gcongr]

Depends on / 依赖: Quotient, Quotient.mk_add, SModEq, SModEq.def, mk_add, simp_rw
-/
theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_add, hxy₁, hxy₂]

@[gcongr]
/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: {ι} {s : Finset ι} {x y : ι -> M}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.sum_cons, Finset.sum_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj => hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]

中文:
定理 求和
  结论: {ι} {s : 有限集 ι} {x y : ι -> M}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.sum_cons, Finset.sum_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj => hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.mem_cons_of_mem, Finset.mem_cons_self, Finset.sum_cons, SModEq, SModEq.rfl, cons_induction, mem_cons_of_mem, mem_cons_self, sum_cons
-/
theorem sum {ι} {s : Finset ι} {x y : ι -> M}
    (hxy : forall i in s, x i ≡ y i [SMOD U]) : ∑ i in s, x i ≡ ∑ i in s, y i [SMOD U] := by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.sum_cons, Finset.sum_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj => hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (hxy : x ≡ y [SMOD U]) (c : R)
  statement: c • x ≡ c • y [SMOD U]
  proof: by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]

中文:
定理 smul
  条件: (hxy : x ≡ y [SMOD U]) (c : R)
  结论: c • x ≡ c • y [SMOD U]
  证明: by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]

Depends on / 依赖: Quotient, Quotient.mk_smul, SModEq, SModEq.def, mk_smul, simp_rw
-/
theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
/--
lemma `nsmul` / 引理 `nsmul`

English:
lemma nsmul
  given: (hxy : x ≡ y [SMOD U]) (n : Nat)
  statement: n • x ≡ n • y [SMOD U]
  proof: by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]

中文:
引理 nsmul
  条件: (hxy : x ≡ y [SMOD U]) (n : 自然数)
  结论: n • x ≡ n • y [SMOD U]
  证明: by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]

Depends on / 依赖: Quotient, Quotient.mk_smul, SModEq, SModEq.def, mk_smul, simp_rw
-/
lemma nsmul (hxy : x ≡ y [SMOD U]) (n : Nat) : n • x ≡ n • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
/--
lemma `zsmul` / 引理 `zsmul`

English:
lemma zsmul
  given: (hxy : x ≡ y [SMOD U]) (n : Int)
  statement: n • x ≡ n • y [SMOD U]
  proof: by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]

中文:
引理 zsmul
  条件: (hxy : x ≡ y [SMOD U]) (n : 整数)
  结论: n • x ≡ n • y [SMOD U]
  证明: by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]

Depends on / 依赖: Quotient, Quotient.mk_smul, SModEq, SModEq.def, mk_smul, simp_rw
-/
lemma zsmul (hxy : x ≡ y [SMOD U]) (n : Int) : n • x ≡ n • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
  proof: by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_mul] at hxy₁ hxy₂ ⊢
  rw [hxy₁]; rw [hxy₂]

@[gcongr]

中文:
定理 mul
  结论: {I : 理想 A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
  证明: by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_mul] at hxy₁ hxy₂ ⊢
  rw [hxy₁]; rw [hxy₂]

@[gcongr]

Depends on / 依赖: Ideal.Quotient.mk_eq_mk, Quotient, SModEq, SModEq.def, map_mul, mk_eq_mk
-/
theorem mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
    (hxy₂ : x₂ ≡ y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_mul] at hxy₁ hxy₂ ⊢
  rw [hxy₁]; rw [hxy₂]

@[gcongr]
/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  statement: {I : Ideal A} {ι} {s : Finset ι} {x y : ι -> A}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.prod_cons, Finset.prod_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj => hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]

中文:
定理 乘积
  结论: {I : 理想 A} {ι} {s : 有限集 ι} {x y : ι -> A}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.prod_cons, Finset.prod_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj => hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.mem_cons_of_mem, Finset.mem_cons_self, Finset.prod_cons, SModEq, SModEq.rfl, cons_induction, mem_cons_of_mem, mem_cons_self, prod_cons
-/
theorem prod {I : Ideal A} {ι} {s : Finset ι} {x y : ι -> A}
    (hxy : forall i in s, x i ≡ y i [SMOD I]) : ∏ i in s, x i ≡ ∏ i in s, y i [SMOD I] := by
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.prod_cons, Finset.prod_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj => hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]
/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: {I : Ideal A} {x y : A} (n : Nat) (hxy : x ≡ y [SMOD I])
  proof: by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_pow] at hxy ⊢
  rw [hxy]

@[gcongr]

中文:
引理 pow
  条件: {I : 理想 A} {x y : A} (n : 自然数) (hxy : x ≡ y [SMOD I])
  证明: by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_pow] at hxy ⊢
  rw [hxy]

@[gcongr]

Depends on / 依赖: Ideal.Quotient.mk_eq_mk, Quotient, SModEq, SModEq.def, map_pow, mk_eq_mk
-/
lemma pow {I : Ideal A} {x y : A} (n : Nat) (hxy : x ≡ y [SMOD I]) :
    x ^ n ≡ y ^ n [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_pow] at hxy ⊢
  rw [hxy]

@[gcongr]
/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: (hxy : x ≡ y [SMOD U])
  statement: -x ≡ - y [SMOD U]
  proof: by
  simpa only [SModEq.def, Quotient.mk_neg, neg_inj]

@[gcongr]

中文:
引理 neg
  条件: (hxy : x ≡ y [SMOD U])
  结论: -x ≡ - y [SMOD U]
  证明: by
  simpa only [SModEq.def, Quotient.mk_neg, neg_inj]

@[gcongr]

Depends on / 依赖: Quotient, Quotient.mk_neg, SModEq, SModEq.def, mk_neg, neg_inj
-/
lemma neg (hxy : x ≡ y [SMOD U]) : -x ≡ - y [SMOD U] := by
  simpa only [SModEq.def, Quotient.mk_neg, neg_inj]

@[gcongr]
/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  given: (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U])
  statement: x₁ - x₂ ≡ y₁ - y₂ [SMOD U]
  proof: by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_sub, hxy₁, hxy₂]

中文:
引理 sub
  条件: (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U])
  结论: x₁ - x₂ ≡ y₁ - y₂ [SMOD U]
  证明: by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_sub, hxy₁, hxy₂]

Depends on / 依赖: Quotient, Quotient.mk_sub, SModEq, SModEq.def, mk_sub, simp_rw
-/
lemma sub (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ - x₂ ≡ y₁ - y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_sub, hxy₁, hxy₂]

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: x ≡ 0 [SMOD U] ↔ x in U
  proof: by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]

中文:
定理 zero
  结论: x ≡ 0 [SMOD U] ↔ x in U
  证明: by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]

Depends on / 依赖: Quotient, SModEq, SModEq.def, Submodule, Submodule.Quotient.eq, sub_zero
-/
theorem zero : x ≡ 0 [SMOD U] ↔ x in U := by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]

/--
theorem `_root_.sub_smodEq_zero` / 定理 `_root_.sub_smodEq_zero`

English:
theorem _root_.sub_smodEq_zero
  statement: x - y ≡ 0 [SMOD U] ↔ x ≡ y [SMOD U]
  proof: by
  simp only [SModEq.sub_mem, sub_zero]

中文:
定理 _root_.sub_smodEq_zero
  结论: x - y ≡ 0 [SMOD U] ↔ x ≡ y [SMOD U]
  证明: by
  simp only [SModEq.sub_mem, sub_zero]

Depends on / 依赖: SModEq, SModEq.sub_mem, sub_mem, sub_zero
-/
theorem _root_.sub_smodEq_zero : x - y ≡ 0 [SMOD U] ↔ x ≡ y [SMOD U] := by
  simp only [SModEq.sub_mem, sub_zero]

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (hxy : x ≡ y [SMOD U]) (f : M ->ₗ[R] N)
  statement: f x ≡ f y [SMOD U.map f]
  proof: (Submodule.Quotient.eq _).2 f.map_sub x y ▸ mem_map_of_mem (Submodule.Quotient.eq _).1 hxy

中文:
定理 map
  条件: (hxy : x ≡ y [SMOD U]) (f : M ->ₗ[R] N)
  结论: f x ≡ f y [SMOD U.map f]
  证明: (Submodule.Quotient.eq _).2 f.map_sub x y ▸ mem_map_of_mem (Submodule.Quotient.eq _).1 hxy

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.eq, f.map_sub, map_sub, mem_map_of_mem
-/
theorem map (hxy : x ≡ y [SMOD U]) (f : M ->ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
(Submodule.Quotient.eq _).2 f.map_sub x y ▸ mem_map_of_mem (Submodule.Quotient.eq _).1 hxy

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  given: {f : M ->ₗ[R] N} (hxy : f x ≡ f y [SMOD V])
  statement: x ≡ y [SMOD V.comap f]
  proof: (Submodule.Quotient.eq _).2
    show f (x - y) in V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy

@[gcongr]

中文:
定理 comap
  条件: {f : M ->ₗ[R] N} (hxy : f x ≡ f y [SMOD V])
  结论: x ≡ y [SMOD V.comap f]
  证明: (Submodule.Quotient.eq _).2
    show f (x - y) in V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy

@[gcongr]

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.eq, f.map_sub, map_sub
-/
theorem comap {f : M ->ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
(Submodule.Quotient.eq _).2
    show f (x - y) in V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy

@[gcongr]
/--
theorem `eval` / 定理 `eval`

English:
theorem eval
  given: {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X])
  proof: by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  gcongr

中文:
定理 eval
  条件: {R : 类型} [交换环 R] {I : 理想 R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X])
  证明: by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  gcongr

Depends on / 依赖: Polynomial, Polynomial.eval_eq_sum, Polynomial.sum, eval_eq_sum, simp_rw
-/
theorem eval {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X]) :
    f.eval x ≡ f.eval y [SMOD I] := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  gcongr

variable (S) in
/--
theorem `restrictScalars` / 定理 `restrictScalars`

English:
theorem restrictScalars
  given: [SMul S R] [IsScalarTower S R M]
  statement: x ≡ y [SMOD U.restrictScalars S] ↔
  proof: by simp [SModEq.sub_mem]

中文:
定理 restrictScalars
  条件: [标量乘法 S R] [标量塔 S R M]
  结论: x ≡ y [SMOD U.restrictScalars S] ↔
  证明: by simp [SModEq.sub_mem]

Depends on / 依赖: SModEq, SModEq.sub_mem, sub_mem
-/
theorem restrictScalars [SMul S R] [IsScalarTower S R M] : x ≡ y [SMOD U.restrictScalars S] ↔
    x ≡ y [SMOD U] := by simp [SModEq.sub_mem]

/--
theorem `idealQuotientMk` / 定理 `idealQuotientMk`

English:
theorem idealQuotientMk
  given: {R : Type*} [CommRing R] {I : Ideal R} {x y : R}
  proof: Iff.rfl

中文:
定理 idealQuotientMk
  条件: {R : 类型} [交换环 R] {I : 理想 R} {x y : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem idealQuotientMk {R : Type*} [CommRing R] {I : Ideal R} {x y : R} :
    x ≡ y [SMOD I] ↔ Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := Iff.rfl

section Pointwise

open scoped Pointwise

@[simp]
/--
theorem `_root_.Submodule.vadd_set_subset_vadd_set_iff` / 定理 `_root_.Submodule.vadd_set_subset_vadd_set_iff`

English:
theorem _root_.Submodule.vadd_set_subset_vadd_set_iff
  proof: by
  rw [SModEq.sub_mem]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub] at h
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using h U.zero_mem
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub]
    intro

中文:
定理 _root_.子模.vadd_set_subset_vadd_set_iff
  证明: by
  rw [SModEq.sub_mem]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub] at h
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using h U.zero_mem
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub]
    intro

Depends on / 依赖: SModEq, SModEq.sub_mem, Set.mem_vadd_set_iff_neg_vadd_mem, Set.vadd_set_subset_iff_subset_neg_vadd_set, U.add_mem, U.zero_mem, add_mem, mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub, sub_mem, vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, zero_mem
-/
theorem _root_.Submodule.vadd_set_subset_vadd_set_iff :
    x +ᵥ (U : Set M) subseteq y +ᵥ (U : Set M) ↔ x ≡ y [SMOD U] := by
  rw [SModEq.sub_mem]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub] at h
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using h U.zero_mem
  · rw [Set.vadd_set_subset_iff_subset_neg_vadd_set, vadd_vadd, neg_add_eq_sub]
    intro z hz
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using U.add_mem h hz

@[simp]
/--
theorem `_root_.Submodule.vadd_set_eq_vadd_set_iff` / 定理 `_root_.Submodule.vadd_set_eq_vadd_set_iff`

English:
theorem _root_.Submodule.vadd_set_eq_vadd_set_iff
  proof: ⟨fun h => Submodule.vadd_set_subset_vadd_set_iff.mp h.subset,
    fun h => Set.Subset.antisymm (Submodule.vadd_set_subset_vadd_set_iff.mpr h)
      (Submodule.vadd_set_subset_vadd_set_iff.mpr h.symm)⟩

中文:
定理 _root_.子模.vadd_set_eq_vadd_set_iff
  证明: ⟨fun h => Submodule.vadd_set_subset_vadd_set_iff.mp h.subset,
    fun h => Set.Subset.antisymm (Submodule.vadd_set_subset_vadd_set_iff.mpr h)
      (Submodule.vadd_set_subset_vadd_set_iff.mpr h.symm)⟩

Depends on / 依赖: Set.Subset.antisymm, Submodule, Submodule.vadd_set_subset_vadd_set_iff.mp, Submodule.vadd_set_subset_vadd_set_iff.mpr, Subset, antisymm, h.subset, h.symm, subset, vadd_set_subset_vadd_set_iff
-/
theorem _root_.Submodule.vadd_set_eq_vadd_set_iff :
    x +ᵥ (U : Set M) = y +ᵥ (U : Set M) ↔ x ≡ y [SMOD U] :=
  ⟨fun h => Submodule.vadd_set_subset_vadd_set_iff.mp h.subset,
    fun h => Set.Subset.antisymm (Submodule.vadd_set_subset_vadd_set_iff.mpr h)
      (Submodule.vadd_set_subset_vadd_set_iff.mpr h.symm)⟩

end Pointwise

end SModEq
