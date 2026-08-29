/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
module

public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
/-!
# Modifying skew monoid algebra at exactly one point

This file contains basic results on updating/erasing an element of a skew monoid algebra using
one point of the domain.
-/

@[expose] public section

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section erase

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: : SkewMonoidAlgebra M α ->+ SkewMonoidAlgebra M α where
  body: ⟨f.coeff.erase a⟩
  map_zero' := by simp
  map_add' := by simp

@[deprecated (since := "2026-07-04")] alias erase_apply_toFinsupp := coeff_erase_apply

@[simp]

中文:
定义 erase
  签名: : 斜幺半群代数 M α ->+ 斜幺半群代数 M α where
  定义体: ⟨f.coeff.erase a⟩
  map_zero' := by simp
  map_add' := by simp

@[deprecated (since := "2026-07-04")] alias erase_apply_toFinsupp := coeff_erase_apply

@[simp]
-/
@[simps] def erase : SkewMonoidAlgebra M α ->+ SkewMonoidAlgebra M α where
  toFun f := ⟨f.coeff.erase a⟩
  map_zero' := by simp
  map_add' := by simp

@[deprecated (since := "2026-07-04")] alias erase_apply_toFinsupp := coeff_erase_apply

@[simp]
/--
theorem `support_erase` / 定理 `support_erase`

English:
theorem support_erase
  given: [DecidableEq α]
  statement: (f.erase a).support = f.support.erase a
  proof: by
  ext; simp [erase]

@[deprecated Finsupp.erase_same (since := "2026-07-04")]

中文:
定理 support_erase
  条件: [DecidableEq α]
  结论: (f.erase a).support = f.support.erase a
  证明: by
  ext; simp [erase]

@[deprecated Finsupp.erase_same (since := "2026-07-04")]
-/
theorem support_erase [DecidableEq α] : (f.erase a).support = f.support.erase a := by
  ext; simp [erase]

@[deprecated Finsupp.erase_same (since := "2026-07-04")]
/--
theorem `coeff_erase_same` / 定理 `coeff_erase_same`

English:
theorem coeff_erase_same
  statement: (f.erase a).coeff a = 0
  proof: by
  simp [erase]

中文:
定理 coeff_erase_same
  结论: (f.erase a).coeff a = 0
  证明: by
  simp [erase]
-/
theorem coeff_erase_same : (f.erase a).coeff a = 0 := by
  simp [erase]

variable {a a'} in
@[deprecated Finsupp.erase_ne (since := "2026-07-04")]
/--
theorem `coeff_erase_ne` / 定理 `coeff_erase_ne`

English:
theorem coeff_erase_ne
  given: (h : a' != a)
  statement: (f.erase a).coeff a' = f.coeff a'
  proof: by
  simp [erase, h]

@[simp]

中文:
定理 coeff_erase_ne
  条件: (h : a' != a)
  结论: (f.erase a).coeff a' = f.coeff a'
  证明: by
  simp [erase, h]

@[simp]
-/
theorem coeff_erase_ne (h : a' != a) : (f.erase a).coeff a' = f.coeff a' := by
  simp [erase, h]

@[simp]
/--
theorem `erase_single` / 定理 `erase_single`

English:
theorem erase_single
  statement: erase a (single a b) = 0
  proof: by
  simp [erase]

中文:
定理 erase_single
  结论: erase a (single a b) = 0
  证明: by
  simp [erase]
-/
theorem erase_single : erase a (single a b) = 0 := by
  simp [erase]

/--
theorem `single_add_erase` / 定理 `single_add_erase`

English:
theorem single_add_erase
  given: (a : α) (f : SkewMonoidAlgebra M α)
  proof: by
  ext; simp [ coeff_add, Finsupp.single_add_erase]

@[elab_as_elim]

中文:
定理 single_add_erase
  条件: (a : α) (f : 斜幺半群代数 M α)
  证明: by
  ext; simp [ coeff_add, Finsupp.single_add_erase]

@[elab_as_elim]

Depends on / 依赖: Finsupp, Finsupp.single_add_erase, coeff_add, single_add_erase
-/
theorem single_add_erase (a : α) (f : SkewMonoidAlgebra M α) :
    single a (f.coeff a) + f.erase a = f := by
  ext; simp [ coeff_add, Finsupp.single_add_erase]

@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {p : SkewMonoidAlgebra M α -> Prop} (f : SkewMonoidAlgebra M α) (h0 : p 0)
  proof: suffices forall (s) (f : SkewMonoidAlgebra M α), f.support = s -> p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
   

中文:
定理 induction
  结论: {p : 斜幺半群代数 M α -> 命题} (f : 斜幺半群代数 M α) (h0 : p 0)
  证明: suffices forall (s) (f : SkewMonoidAlgebra M α), f.support = s -> p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
   

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.erase_cons, Finset.mem_cons_self, Finset.mem_erase, SkewMonoidAlgebra, classical, cons_induction_on, erase_cons, f.coeff, f.erase, f.support, mem_cons_self, mem_erase, mem_support_iff, single, single_add_erase, support, support_eq_empty, support_erase
-/
theorem induction {p : SkewMonoidAlgebra M α -> Prop} (f : SkewMonoidAlgebra M α) (h0 : p 0)
    (ha : forall (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support -> b != 0 -> p f -> p (single a b + f)) :
    p f :=
  suffices forall (s) (f : SkewMonoidAlgebra M α), f.support = s -> p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
    apply ha
    · rw [support_erase, Finset.mem_erase]
      exact fun H => H.1 rfl
    · simp only [← mem_support_iff, hf, Finset.mem_cons_self]
    · apply ih
      rw [support_erase]; rw [hf]; rw [Finset.erase_cons]

end erase

section update

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: : SkewMonoidAlgebra M α
  body: ⟨f.coeff.update a b⟩

@[deprecated (since := "2026-07-04")] alias update_toFinsupp := coeff_update

@[simp]

中文:
定义 update
  签名: : 斜幺半群代数 M α
  定义体: ⟨f.coeff.update a b⟩

@[deprecated (since := "2026-07-04")] alias update_toFinsupp := coeff_update

@[simp]
-/
@[simps coeff] def update : SkewMonoidAlgebra M α :=
  ⟨f.coeff.update a b⟩

@[deprecated (since := "2026-07-04")] alias update_toFinsupp := coeff_update

@[simp]
/--
theorem `update_self` / 定理 `update_self`

English:
theorem update_self
  statement: f.update a (f.coeff a) = f
  proof: by ext; simp

@[simp]

中文:
定理 update_self
  结论: f.update a (f.coeff a) = f
  证明: by ext; simp

@[simp]
-/
theorem update_self : f.update a (f.coeff a) = f := by ext; simp

@[simp]
/--
theorem `zero_update` / 定理 `zero_update`

English:
theorem zero_update
  statement: update 0 a b = single a b
  proof: by
  simp [update]

中文:
定理 zero_update
  结论: update 0 a b = single a b
  证明: by
  simp [update]

Depends on / 依赖: update
-/
theorem zero_update : update 0 a b = single a b := by
  simp [update]

/--
theorem `support_update` / 定理 `support_update`

English:
theorem support_update
  given: [DecidableEq α] [DecidableEq M]
  proof: by
  aesop (add norm [update, Finsupp.support_update_ne_zero])

@[deprecated Finsupp.update_apply (since := "2026-07-04")]

中文:
定理 support_update
  条件: [DecidableEq α] [DecidableEq M]
  证明: by
  aesop (add norm [update, Finsupp.support_update_ne_zero])

@[deprecated Finsupp.update_apply (since := "2026-07-04")]

Depends on / 依赖: Finsupp, Finsupp.support_update_ne_zero, support_update_ne_zero, update
-/
theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  aesop (add norm [update, Finsupp.support_update_ne_zero])

@[deprecated Finsupp.update_apply (since := "2026-07-04")]
/--
theorem `coeff_update_apply` / 定理 `coeff_update_apply`

English:
theorem coeff_update_apply
  given: [DecidableEq α]
  proof: by
  simp [coeff_update, Function.update_apply]

@[deprecated Finsupp.update_apply (since := "2026-07-04")]

中文:
定理 coeff_update_apply
  条件: [DecidableEq α]
  证明: by
  simp [coeff_update, Function.update_apply]

@[deprecated Finsupp.update_apply (since := "2026-07-04")]

Depends on / 依赖: Function, Function.update_apply, coeff_update, update_apply
-/
theorem coeff_update_apply [DecidableEq α] :
    (f.update a b).coeff a' = if a' = a then b else f.coeff a' := by
  simp [coeff_update, Function.update_apply]

@[deprecated Finsupp.update_apply (since := "2026-07-04")]
/--
theorem `coeff_update_same` / 定理 `coeff_update_same`

English:
theorem coeff_update_same
  statement: (f.update a b).coeff a = b
  proof: by
  classical
  rw [f.coeff_update_apply]; rw [if_pos rfl]

中文:
定理 coeff_update_same
  结论: (f.update a b).coeff a = b
  证明: by
  classical
  rw [f.coeff_update_apply]; rw [if_pos rfl]

Depends on / 依赖: classical, coeff_update_apply, f.coeff_update_apply, if_pos
-/
theorem coeff_update_same : (f.update a b).coeff a = b := by
  classical
  rw [f.coeff_update_apply]; rw [if_pos rfl]

variable {a a'} in
@[deprecated Finsupp.update_apply (since := "2026-07-04")]
/--
theorem `coeff_update_ne` / 定理 `coeff_update_ne`

English:
theorem coeff_update_ne
  given: (h : a' != a)
  statement: (f.update a b).coeff a' = f.coeff a'
  proof: by
  classical
  rw [f.coeff_update_apply]; rw [if_neg h]

中文:
定理 coeff_update_ne
  条件: (h : a' != a)
  结论: (f.update a b).coeff a' = f.coeff a'
  证明: by
  classical
  rw [f.coeff_update_apply]; rw [if_neg h]

Depends on / 依赖: classical, coeff_update_apply, f.coeff_update_apply, if_neg
-/
theorem coeff_update_ne (h : a' != a) : (f.update a b).coeff a' = f.coeff a' := by
  classical
  rw [f.coeff_update_apply]; rw [if_neg h]

/--
theorem `update_eq_erase_add_single` / 定理 `update_eq_erase_add_single`

English:
theorem update_eq_erase_add_single
  statement: f.update a b = f.erase a + single a b
  proof: by
  classical ext x; by_cases hx : x = a <;> aesop (add norm coeff_single_apply)

@[simp]

中文:
定理 update_eq_erase_add_single
  结论: f.update a b = f.erase a + single a b
  证明: by
  classical ext x; by_cases hx : x = a <;> aesop (add norm coeff_single_apply)

@[simp]

Depends on / 依赖: classical, coeff_single_apply
-/
theorem update_eq_erase_add_single : f.update a b = f.erase a + single a b := by
  classical ext x; by_cases hx : x = a <;> aesop (add norm coeff_single_apply)

@[simp]
/--
theorem `update_zero_eq_erase` / 定理 `update_zero_eq_erase`

English:
theorem update_zero_eq_erase
  statement: f.update a 0 = f.erase a
  proof: by
  classical ext; simp [coeff_erase_apply, Finsupp.erase_apply, Function.update_apply]

中文:
定理 update_zero_eq_erase
  结论: f.update a 0 = f.erase a
  证明: by
  classical ext; simp [coeff_erase_apply, Finsupp.erase_apply, Function.update_apply]

Depends on / 依赖: Finsupp, Finsupp.erase_apply, Function, Function.update_apply, classical, coeff_erase_apply, erase_apply, update_apply
-/
theorem update_zero_eq_erase : f.update a 0 = f.erase a := by
  classical ext; simp [coeff_erase_apply, Finsupp.erase_apply, Function.update_apply]

end update

end SkewMonoidAlgebra
