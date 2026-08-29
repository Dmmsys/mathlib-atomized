/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Order.Restriction

/-! # Auxiliary maps for Ionescu-Tulcea theorem

This file contains auxiliary maps which are used to prove the Ionescu-Tulcea theorem.
-/

@[expose] public section

open Finset Preorder

section Definitions

section LinearOrder

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι -> Type*}

/--
Definition of `IocProdIoc` / `IocProdIoc` 的定义

English:
definition IocProdIoc
  signature: (a b c : ι) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (i : Ioc a c)
  body: if h : i <= b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

@[fun_prop]

中文:
定义 IocProdIoc
  签名: (a b c : ι) (x : (Π i : 左开右闭区间 a b, X i) × (Π i : 左开右闭区间 b c, X i)) (i : 左开右闭区间 a c)
  定义体: if h : i <= b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

@[fun_prop]

Depends on / 依赖: mem_Ioc, not_le
-/
def IocProdIoc (a b c : ι) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (i : Ioc a c) : X i :=
  if h : i <= b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

@[fun_prop]
/--
lemma `measurable_IocProdIoc` / 引理 `measurable_IocProdIoc`

English:
lemma measurable_IocProdIoc
  given: [forall i, MeasurableSpace (X i)] {a b c : ι}
  proof: by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i <= b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

中文:
引理 measurable_IocProdIoc
  条件: [对任意 i, 可测空间 (X i)] {a b c : ι}
  证明: by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i <= b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

Depends on / 依赖: IocProdIoc, measurable_fst, measurable_fst.eval, measurable_pi_lambda, measurable_snd, measurable_snd.eval
-/
lemma measurable_IocProdIoc [forall i, MeasurableSpace (X i)] {a b c : ι} :
    Measurable (IocProdIoc (X := X) a b c) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i <= b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

variable [LocallyFiniteOrderBot ι]

/--
Definition of `IicProdIoc` / `IicProdIoc` 的定义

English:
definition IicProdIoc
  signature: (a b : ι) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) (i : Iic b)
  body: if h : i <= a
    then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

中文:
定义 IicProdIoc
  签名: (a b : ι) (x : (Π i : 左无界右闭区间 a, X i) × (Π i : 左开右闭区间 a b, X i)) (i : 左无界右闭区间 b)
  定义体: if h : i <= a
    then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

Depends on / 依赖: mem_Iic, mem_Ioc, not_le
-/
def IicProdIoc (a b : ι) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) (i : Iic b) : X i :=
  if h : i <= a
    then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

/--
lemma `IicProdIoc_def` / 引理 `IicProdIoc_def`

English:
lemma IicProdIoc_def
  given: (a b : ι)
  proof: rfl

中文:
引理 IicProdIoc_def
  条件: (a b : ι)
  证明: rfl

Depends on / 依赖: mem_Iic
-/
lemma IicProdIoc_def (a b : ι) :
    IicProdIoc (X := X) a b = fun x i => if h : i.1 <= a then x.1 ⟨i, mem_Iic.2 h⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩ := rfl

/--
lemma `frestrictLe₂_comp_IicProdIoc` / 引理 `frestrictLe₂_comp_IicProdIoc`

English:
lemma frestrictLe₂_comp_IicProdIoc
  given: {a b : ι} (hab : a <= b)
  proof: by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

中文:
引理 frestrictLe₂_comp_IicProdIoc
  条件: {a b : ι} (hab : a <= b)
  证明: by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

Depends on / 依赖: IicProdIoc, Prod.fst, mem_Iic
-/
lemma frestrictLe₂_comp_IicProdIoc {a b : ι} (hab : a <= b) :
    (frestrictLe₂ hab) ∘ (IicProdIoc (X := X) a b) = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

/--
lemma `restrict₂_comp_IicProdIoc` / 引理 `restrict₂_comp_IicProdIoc`

English:
lemma restrict₂_comp_IicProdIoc
  given: (a b : ι)
  proof: by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

@[simp]

中文:
引理 restrict₂_comp_IicProdIoc
  条件: (a b : ι)
  证明: by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

@[simp]

Depends on / 依赖: IicProdIoc, Prod.snd, mem_Ioc, not_le
-/
lemma restrict₂_comp_IicProdIoc (a b : ι) :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

@[simp]
/--
lemma `IicProdIoc_self` / 引理 `IicProdIoc_self`

English:
lemma IicProdIoc_self
  given: (a : ι)
  statement: IicProdIoc (X := X) a a = Prod.fst
  proof: by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

中文:
引理 IicProdIoc_self
  条件: (a : ι)
  结论: IicProdIoc (X := X) a a = 积类型.fst
  证明: by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

Depends on / 依赖: IicProdIoc, Prod.fst, mem_Iic
-/
lemma IicProdIoc_self (a : ι) : IicProdIoc (X := X) a a = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

/--
lemma `IicProdIoc_le` / 引理 `IicProdIoc_le`

English:
lemma IicProdIoc_le
  given: {a b : ι} (hba : b <= a)
  proof: by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]

中文:
引理 IicProdIoc_le
  条件: {a b : ι} (hba : b <= a)
  证明: by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]

Depends on / 依赖: IicProdIoc, Prod.fst, mem_Iic
-/
lemma IicProdIoc_le {a b : ι} (hba : b <= a) :
    IicProdIoc (X := X) a b = (frestrictLe₂ hba) ∘ Prod.fst := by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]

/--
lemma `IicProdIoc_comp_restrict₂` / 引理 `IicProdIoc_comp_restrict₂`

English:
lemma IicProdIoc_comp_restrict₂
  given: {a b : ι}
  proof: by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

中文:
引理 IicProdIoc_comp_restrict₂
  条件: {a b : ι}
  证明: by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

Depends on / 依赖: IicProdIoc, Prod.snd, mem_Ioc, not_le
-/
lemma IicProdIoc_comp_restrict₂ {a b : ι} :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

variable [forall i, MeasurableSpace (X i)]

@[fun_prop]
/--
lemma `measurable_IicProdIoc` / 引理 `measurable_IicProdIoc`

English:
lemma measurable_IicProdIoc
  given: {m n : ι}
  statement: Measurable (IicProdIoc (X := X) m n)
  proof: by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i <= m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

中文:
引理 measurable_IicProdIoc
  条件: {m n : ι}
  结论: 可测 (IicProdIoc (X := X) m n)
  证明: by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i <= m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

Depends on / 依赖: IicProdIoc, measurable_fst, measurable_fst.eval, measurable_pi_lambda, measurable_snd, measurable_snd.eval
-/
lemma measurable_IicProdIoc {m n : ι} : Measurable (IicProdIoc (X := X) m n) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i <= m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

namespace MeasurableEquiv

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IicProdIoc` / `IicProdIoc` 的定义

English:
definition IicProdIoc
  signature: {a b : ι} (hab : a <= b)
  body: if h : i <= a then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
  invFun x := ⟨fun i => x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩, fun i => x ⟨i.1, Ioc_subset_Iic_self i.2⟩⟩
  left_inv := fun x => by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 (mem_Ioc.1 i.2).1]

中文:
定义 IicProdIoc
  签名: {a b : ι} (hab : a <= b)
  定义体: if h : i <= a then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
  invFun x := ⟨fun i => x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩, fun i => x ⟨i.1, Ioc_subset_Iic_self i.2⟩⟩
  left_inv := fun x => by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 (mem_Ioc.1 i.2).1]

Depends on / 依赖: mem_Iic
-/
def IicProdIoc {a b : ι} (hab : a <= b) :
    ((Π i : Iic a, X i) × (Π i : Ioc a b, X i)) ≃ᵐ Π i : Iic b, X i where
  toFun x i := if h : i <= a then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
  invFun x := ⟨fun i => x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩, fun i => x ⟨i.1, Ioc_subset_Iic_self i.2⟩⟩
  left_inv := fun x => by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 (mem_Ioc.1 i.2).1]
  right_inv := fun x => funext fun i => by
    by_cases hi : i.1 <= a <;> simp [hi]
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun x => ?_)
    by_cases h : x <= a
    · simpa [h] using measurable_fst.eval
    · simpa [h] using measurable_snd.eval

/--
lemma `coe_IicProdIoc` / 引理 `coe_IicProdIoc`

English:
lemma coe_IicProdIoc
  given: {a b : ι} (hab : a <= b)
  proof: rfl

中文:
引理 coe_IicProdIoc
  条件: {a b : ι} (hab : a <= b)
  证明: rfl

Depends on / 依赖: IicProdIoc, _root_, _root_.IicProdIoc
-/
lemma coe_IicProdIoc {a b : ι} (hab : a <= b) :
    ⇑(IicProdIoc (X := X) hab) = _root_.IicProdIoc a b := rfl

/--
lemma `coe_IicProdIoc_symm` / 引理 `coe_IicProdIoc_symm`

English:
lemma coe_IicProdIoc_symm
  given: {a b : ι} (hab : a <= b)
  proof: rfl

中文:
引理 coe_IicProdIoc_symm
  条件: {a b : ι} (hab : a <= b)
  证明: rfl
-/
lemma coe_IicProdIoc_symm {a b : ι} (hab : a <= b) :
    ⇑(IicProdIoc (X := X) hab).symm =
    fun x => (frestrictLe₂ hab x, restrict₂ Ioc_subset_Iic_self x) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IicProdIoi` / `IicProdIoi` 的定义

English:
definition IicProdIoi
  signature: (a : ι)
  body: fun x i => if hi : i <= a
    then x.1 ⟨i, mem_Iic.2 hi⟩
    else x.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
  invFun := fun x => (fun i => x i, fun i => x i)
  left_inv := fun x => by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
  right_inv := fun x => by simp
  measura

中文:
定义 IicProdIoi
  签名: (a : ι)
  定义体: fun x i => if hi : i <= a
    then x.1 ⟨i, mem_Iic.2 hi⟩
    else x.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
  invFun := fun x => (fun i => x i, fun i => x i)
  left_inv := fun x => by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
  right_inv := fun x => by simp
  measura
-/
def IicProdIoi (a : ι) :
    ((Π i : Iic a, X i) × (Π i : Set.Ioi a, X i)) ≃ᵐ (Π n, X n) where
  toFun := fun x i => if hi : i <= a
    then x.1 ⟨i, mem_Iic.2 hi⟩
    else x.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
  invFun := fun x => (fun i => x i, fun i => x i)
  left_inv := fun x => by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
  right_inv := fun x => by simp
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases hi : i <= a <;> simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]
    · exact measurable_fst.eval
    · exact measurable_snd.eval

end MeasurableEquiv

end LinearOrder

section Nat

variable {X : Nat -> Type*} [forall n, MeasurableSpace (X n)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `MeasurableEquiv.piSingleton` / `MeasurableEquiv.piSingleton` 的定义

English:
definition MeasurableEquiv.piSingleton
  signature: (a : Nat)
  body: (Nat.mem_Ioc_succ.1 i.2).symm ▸ x
  invFun x := x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x => by simp
  right_inv := fun x => funext fun i => by cases Nat.mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i => (Measura

中文:
定义 可测等价.piSingleton
  签名: (a : 自然数)
  定义体: (Nat.mem_Ioc_succ.1 i.2).symm ▸ x
  invFun x := x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x => by simp
  right_inv := fun x => funext fun i => by cases Nat.mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i => (Measura

Depends on / 依赖: Nat.mem_Ioc_succ, mem_Ioc_succ
-/
def MeasurableEquiv.piSingleton (a : Nat) : X (a + 1) ≃ᵐ Π i : Ioc a (a + 1), X i where
  toFun x i := (Nat.mem_Ioc_succ.1 i.2).symm ▸ x
  invFun x := x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x => by simp
  right_inv := fun x => funext fun i => by cases Nat.mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i => (MeasurableEquiv.cast _ ?_).measurable)
    cases Nat.mem_Ioc_succ' i; rfl

end Nat

end Definitions

section Lemmas

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι -> Type*}

/--
lemma `_root_.IocProdIoc_preimage` / 引理 `_root_.IocProdIoc_preimage`

English:
lemma _root_.IocProdIoc_preimage
  statement: {a b c : ι} (hab : a <= b) (hbc : b <= c)
  proof: by
  ext x
  simp
  grind [IocProdIoc]

中文:
引理 _root_.IocProdIoc_preimage
  结论: {a b c : ι} (hab : a <= b) (hbc : b <= c)
  证明: by
  ext x
  simp
  grind [IocProdIoc]

Depends on / 依赖: Ioc_subset_Ioc_right
-/
lemma _root_.IocProdIoc_preimage {a b c : ι} (hab : a <= b) (hbc : b <= c)
    (s : (i : Ioc a c) -> Set (X i)) :
    IocProdIoc a b c ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| restrict₂ (π := (fun n => Set (X n))) (Ioc_subset_Ioc_right hbc) s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n => Set (X n))) (Ioc_subset_Ioc_left hab) s) := by
  ext x
  simp
  grind [IocProdIoc]

variable [LocallyFiniteOrderBot ι]

/--
lemma `_root_.IicProdIoc_preimage` / 引理 `_root_.IicProdIoc_preimage`

English:
lemma _root_.IicProdIoc_preimage
  given: {a b : ι} (hab : a <= b) (s : (i : Iic b) -> Set (X i))
  proof: by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc_def, forall_const,
    Subtype.forall, mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h => ⟨fun i hi => ?_, fun i ⟨hi1, hi2⟩ => ?_⟩, fun ⟨h1, h2⟩ i hi => ?_⟩
  · convert! h i (hi.trans hab)
 

中文:
引理 _root_.IicProdIoc_preimage
  条件: {a b : ι} (hab : a <= b) (s : (i : 左无界右闭区间 b) -> 集合 (X i))
  证明: by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc_def, forall_const,
    Subtype.forall, mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h => ⟨fun i hi => ?_, fun i ⟨hi1, hi2⟩ => ?_⟩, fun ⟨h1, h2⟩ i hi => ?_⟩
  · convert! h i (hi.trans hab)
 
-/
lemma _root_.IicProdIoc_preimage {a b : ι} (hab : a <= b) (s : (i : Iic b) -> Set (X i)) :
    IicProdIoc a b ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| frestrictLe₂ (π := (fun n => Set (X n))) hab s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n => Set (X n))) Ioc_subset_Iic_self s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc_def, forall_const,
    Subtype.forall, mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h => ⟨fun i hi => ?_, fun i ⟨hi1, hi2⟩ => ?_⟩, fun ⟨h1, h2⟩ i hi => ?_⟩
  · convert! h i (hi.trans hab)
    rw [dif_pos hi]
  · convert! h i hi2
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i hi3
    · exact h2 i ⟨not_le.1 hi3, hi⟩

end Lemmas
