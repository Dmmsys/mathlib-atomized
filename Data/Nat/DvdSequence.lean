/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Divisibility sequences

A sequence `f : ℕ → ℕ` is a *divisibility sequence* if it satisfies `f a ∣ f b` whenever `a ∣ b`.

A sequence `f : ℕ → ℕ` is a *strong divisibility sequence* if `gcd (f a) (f b) = f (gcd a b)`.

This file defines divisibility sequences and strong divisibility sequences, and provides some basic
API for these definitions.

## Main definitions

* `IsDvdSeq`: A function `f` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`.
* `Nat.IsStrongDvdSeq`: A function `f : ℕ → ℕ` is a strong divisibility sequence if `f` satisfies
  `gcd (f a) (f b) = f (gcd a b)`.
-/

@[expose] public section

variable {α β γ : Type*}

-- this lemma regarding interaction between `smul` and `dvd` does not have a good home in mathlib
/--
lemma `smul_dvd_smul` / 引理 `smul_dvd_smul`

English:
lemma smul_dvd_smul
  statement: [Monoid α] [Monoid β] [SMul α β] [IsScalarTower α β β]
  proof: by
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab, hcd
  exact ⟨x • y, mul_smul_mul_comm a x c y⟩

中文:
引理 smul_dvd_smul
  结论: [Monoid α] [Monoid β] [SMul α β] [IsScalarTower α β β]
  证明: by
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab, hcd
  exact ⟨x • y, mul_smul_mul_comm a x c y⟩

Depends on / 依赖: mul_smul_mul_comm
-/
lemma smul_dvd_smul [Monoid α] [Monoid β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] {a b : α} {c d : β}
    (hab : a ∣ b) (hcd : c ∣ d) : (a • c) ∣ (b • d) := by
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab, hcd
  exact ⟨x • y, mul_smul_mul_comm a x c y⟩

/--
Definition of `IsDvdSequence` / `IsDvdSequence` 的定义

English:
definition IsDvdSequence
  signature: [Dvd α] [Dvd β] (f : α -> β)
  body: forall a b, a ∣ b -> f a ∣ f b

@[deprecated (since := "2026-06-30")] alias IsDivSequence := IsDvdSequence

中文:
定义 IsDvdSequence
  签名: [Dvd α] [Dvd β] (f : α -> β)
  定义体: forall a b, a ∣ b -> f a ∣ f b

@[deprecated (since := "2026-06-30")] alias IsDivSequence := IsDvdSequence
-/
def IsDvdSequence [Dvd α] [Dvd β] (f : α -> β) : Prop :=
  forall a b, a ∣ b -> f a ∣ f b

@[deprecated (since := "2026-06-30")] alias IsDivSequence := IsDvdSequence

namespace IsDvdSequence

variable (α) in
/--
theorem `id` / 定理 `id`

English:
theorem id
  given: [Dvd α]
  statement: IsDvdSequence (id : α -> α)
  proof: fun _ _ => id

中文:
定理 id
  条件: [Dvd α]
  结论: IsDvdSequence (id : α -> α)
  证明: fun _ _ => id
-/
protected theorem id [Dvd α] : IsDvdSequence (id : α -> α) :=
  fun _ _ => id

variable (α) in
/--
theorem `const` / 定理 `const`

English:
theorem const
  given: [Dvd α] [Monoid β] (b : β)
  statement: IsDvdSequence (fun _ : α => b)
  proof: by
  simp [IsDvdSequence]

中文:
定理 const
  条件: [Dvd α] [Monoid β] (b : β)
  结论: IsDvdSequence (fun _ : α => b)
  证明: by
  simp [IsDvdSequence]
-/
protected theorem const [Dvd α] [Monoid β] (b : β) : IsDvdSequence (fun _ : α => b) := by
  simp [IsDvdSequence]

/--
theorem `smul'` / 定理 `smul'`

English:
theorem smul'
  statement: [Dvd α] [Monoid β] [Monoid γ] {f : α -> β} {g : α -> γ} [SMul β γ]
  proof: fun a b hab => smul_dvd_smul (hf a b hab) (hg a b hab)

中文:
定理 smul'
  结论: [Dvd α] [Monoid β] [Monoid γ] {f : α -> β} {g : α -> γ} [SMul β γ]
  证明: fun a b hab => smul_dvd_smul (hf a b hab) (hg a b hab)
-/
protected theorem smul' [Dvd α] [Monoid β] [Monoid γ] {f : α -> β} {g : α -> γ} [SMul β γ]
    [IsScalarTower β γ γ] [IsScalarTower β β γ] [SMulCommClass β γ γ]
    (hf : IsDvdSequence f) (hg : IsDvdSequence g) : IsDvdSequence (f • g) :=
  fun a b hab => smul_dvd_smul (hf a b hab) (hg a b hab)

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [Dvd α] [CommMonoid β] {f g : α -> β} (hf : IsDvdSequence f)
  proof: .smul' hf hg

中文:
定理 mul
  结论: [Dvd α] [CommMonoid β] {f g : α -> β} (hf : IsDvdSequence f)
  证明: .smul' hf hg
-/
protected theorem mul [Dvd α] [CommMonoid β] {f g : α -> β} (hf : IsDvdSequence f)
    (hg : IsDvdSequence g) : IsDvdSequence (f * g) :=
  .smul' hf hg

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: [Dvd α] [Monoid β] [Monoid γ] {f : α -> γ} [SMul β γ] [IsScalarTower β γ γ]
  proof: .smul' (.const α b) hg

中文:
定理 smul
  结论: [Dvd α] [Monoid β] [Monoid γ] {f : α -> γ} [SMul β γ] [IsScalarTower β γ γ]
  证明: .smul' (.const α b) hg
-/
protected theorem smul [Dvd α] [Monoid β] [Monoid γ] {f : α -> γ} [SMul β γ] [IsScalarTower β γ γ]
    [IsScalarTower β β γ] [SMulCommClass β γ γ] (b : β) (hg : IsDvdSequence f) :
    IsDvdSequence (b • f) :=
  .smul' (.const α b) hg

end IsDvdSequence

@[deprecated (since := "2026-06-30")] alias IsDivSequence.smul := IsDvdSequence.smul
@[deprecated (since := "2026-06-30")] alias isDivSequence_id := IsDvdSequence.id

namespace Nat

/--
Definition of `IsStrongDvdSequence` / `IsStrongDvdSequence` 的定义

English:
definition IsStrongDvdSequence
  signature: (f : Nat -> Nat)
  body: forall a b, (f a).gcd (f b) = f (a.gcd b)

中文:
定义 IsStrongDvdSequence
  签名: (f : 自然数 -> 自然数)
  定义体: forall a b, (f a).gcd (f b) = f (a.gcd b)

Depends on / 依赖: a.gcd
-/
def IsStrongDvdSequence (f : Nat -> Nat) : Prop :=
  forall a b, (f a).gcd (f b) = f (a.gcd b)

namespace IsStrongDvdSequence

/--
theorem `isDvdSequence` / 定理 `isDvdSequence`

English:
theorem isDvdSequence
  given: {f : Nat -> Nat} (hf : IsStrongDvdSequence f)
  statement: IsDvdSequence f
  proof: by
  intro a b hab
  simpa [gcd_eq_left hab, gcd_eq_left_iff_dvd] using hf a b

中文:
定理 isDvdSequence
  条件: {f : 自然数 -> 自然数} (hf : IsStrongDvdSequence f)
  结论: IsDvdSequence f
  证明: by
  intro a b hab
  simpa [gcd_eq_left hab, gcd_eq_left_iff_dvd] using hf a b

Depends on / 依赖: gcd_eq_left, gcd_eq_left_iff_dvd
-/
theorem isDvdSequence {f : Nat -> Nat} (hf : IsStrongDvdSequence f) : IsDvdSequence f := by
  intro a b hab
  simpa [gcd_eq_left hab, gcd_eq_left_iff_dvd] using hf a b

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsStrongDvdSequence (id : Nat -> Nat)
  proof: fun _ _ => rfl

中文:
定理 id
  结论: IsStrongDvdSequence (id : 自然数 -> 自然数)
  证明: fun _ _ => rfl
-/
protected theorem id : IsStrongDvdSequence (id : Nat -> Nat) :=
  fun _ _ => rfl

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (n : Nat)
  statement: IsStrongDvdSequence (fun _ => n)
  proof: by
  simp [IsStrongDvdSequence]

中文:
定理 const
  条件: (n : 自然数)
  结论: IsStrongDvdSequence (fun _ => n)
  证明: by
  simp [IsStrongDvdSequence]
-/
protected theorem const (n : Nat) : IsStrongDvdSequence (fun _ => n) := by
  simp [IsStrongDvdSequence]

end IsStrongDvdSequence

end Nat
