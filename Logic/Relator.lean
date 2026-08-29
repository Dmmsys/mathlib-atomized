/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Relator for functions, pairs, sums, and lists.
-/

@[expose] public section

namespace Relator
universe u₁ u₂ v₁ v₂

/- TODO(johoelzl):
* should we introduce relators of datatypes as recursive function or as inductive
  predicate? For now we stick to the recursor approach.
* relation lift for datatypes, Π, Σ, set, and subtype types
* proof composition and identity laws
* implement method to derive relators from datatype
-/

section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α -> β -> Prop) (S : γ -> δ -> Prop)

/--
Definition of `LiftFun` / `LiftFun` 的定义

English:
definition LiftFun
  signature: (f : α -> γ) (g : β -> δ)
  body: forall ⦃a b⦄, R a b -> S (f a) (g b)

中文:
定义 LiftFun
  签名: (f : α -> γ) (g : β -> δ)
  定义体: forall ⦃a b⦄, R a b -> S (f a) (g b)
-/
def LiftFun (f : α -> γ) (g : β -> δ) : Prop :=
  forall ⦃a b⦄, R a b -> S (f a) (g b)

/-- `(R ⇒ S) f g` means `LiftFun R S f g`. -/
scoped infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Sort u₁} {β : Sort u₂} (R : α -> β -> Prop)

/--
Definition of `RightTotal` / `RightTotal` 的定义

English:
definition RightTotal
  signature: : Prop
  body: forall b, exists a, R a b

中文:
定义 RightTotal
  签名: : 命题
  定义体: forall b, exists a, R a b
-/
def RightTotal : Prop := forall b, exists a, R a b

/--
Definition of `LeftTotal` / `LeftTotal` 的定义

English:
definition LeftTotal
  signature: : Prop
  body: forall a, exists b, R a b

中文:
定义 LeftTotal
  签名: : 命题
  定义体: forall a, exists b, R a b
-/
def LeftTotal : Prop := forall a, exists b, R a b

/--
Definition of `BiTotal` / `BiTotal` 的定义

English:
definition BiTotal
  signature: : Prop
  body: LeftTotal R ∧ RightTotal R

中文:
定义 BiTotal
  签名: : 命题
  定义体: LeftTotal R ∧ RightTotal R

Depends on / 依赖: LeftTotal, RightTotal
-/
def BiTotal : Prop := LeftTotal R ∧ RightTotal R

/--
Definition of `LeftUnique` / `LeftUnique` 的定义

English:
definition LeftUnique
  signature: : Prop
  body: forall ⦃a b c⦄, R a c -> R b c -> a = b

中文:
定义 LeftUnique
  签名: : 命题
  定义体: forall ⦃a b c⦄, R a c -> R b c -> a = b
-/
def LeftUnique : Prop := forall ⦃a b c⦄, R a c -> R b c -> a = b

/--
Definition of `RightUnique` / `RightUnique` 的定义

English:
definition RightUnique
  signature: : Prop
  body: forall ⦃a b c⦄, R a b -> R a c -> b = c

中文:
定义 RightUnique
  签名: : 命题
  定义体: forall ⦃a b c⦄, R a b -> R a c -> b = c
-/
def RightUnique : Prop := forall ⦃a b c⦄, R a b -> R a c -> b = c

/--
Definition of `BiUnique` / `BiUnique` 的定义

English:
definition BiUnique
  signature: : Prop
  body: LeftUnique R ∧ RightUnique R

中文:
定义 BiUnique
  签名: : 命题
  定义体: LeftUnique R ∧ RightUnique R

Depends on / 依赖: LeftUnique, RightUnique
-/
def BiUnique : Prop := LeftUnique R ∧ RightUnique R

variable {R}

/--
lemma `RightTotal.rel_forall` / 引理 `RightTotal.rel_forall`

English:
lemma RightTotal.rel_forall
  given: (h : RightTotal R)
  proof: fun _ _ Hrel H b => Exists.elim (h b) (fun _ Rab => Hrel Rab (H _))

中文:
引理 RightTotal.rel_对任意
  条件: (h : RightTotal R)
  证明: fun _ _ Hrel H b => Exists.elim (h b) (fun _ Rab => Hrel Rab (H _))

Depends on / 依赖: Exists, Exists.elim
-/
lemma RightTotal.rel_forall (h : RightTotal R) :
    ((R ⇒ (· -> ·)) ⇒ (· -> ·)) (fun p => forall i, p i) (fun q => forall i, q i) :=
  fun _ _ Hrel H b => Exists.elim (h b) (fun _ Rab => Hrel Rab (H _))

/--
lemma `LeftTotal.rel_exists` / 引理 `LeftTotal.rel_exists`

English:
lemma LeftTotal.rel_exists
  given: (h : LeftTotal R)
  proof: fun _ _ Hrel ⟨a, pa⟩ => (h a).imp fun _ Rab => Hrel Rab pa

中文:
引理 LeftTotal.rel_存在
  条件: (h : LeftTotal R)
  证明: fun _ _ Hrel ⟨a, pa⟩ => (h a).imp fun _ Rab => Hrel Rab pa
-/
lemma LeftTotal.rel_exists (h : LeftTotal R) :
    ((R ⇒ (· -> ·)) ⇒ (· -> ·)) (fun p => exists i, p i) (fun q => exists i, q i) :=
  fun _ _ Hrel ⟨a, pa⟩ => (h a).imp fun _ Rab => Hrel Rab pa

/--
lemma `BiTotal.rel_forall` / 引理 `BiTotal.rel_forall`

English:
lemma BiTotal.rel_forall
  given: (h : BiTotal R)
  proof: fun _ _ Hrel =>
    ⟨fun H b => Exists.elim (h.right b) (fun _ Rab => (Hrel Rab).mp (H _)),
      fun H a => Exists.elim (h.left a) (fun _ Rab => (Hrel Rab).mpr (H _))⟩

中文:
引理 BiTotal.rel_对任意
  条件: (h : BiTotal R)
  证明: fun _ _ Hrel =>
    ⟨fun H b => Exists.elim (h.right b) (fun _ Rab => (Hrel Rab).mp (H _)),
      fun H a => Exists.elim (h.left a) (fun _ Rab => (Hrel Rab).mpr (H _))⟩

Depends on / 依赖: Exists, Exists.elim, h.left, h.right
-/
lemma BiTotal.rel_forall (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => forall i, p i) (fun q => forall i, q i) :=
  fun _ _ Hrel =>
    ⟨fun H b => Exists.elim (h.right b) (fun _ Rab => (Hrel Rab).mp (H _)),
      fun H a => Exists.elim (h.left a) (fun _ Rab => (Hrel Rab).mpr (H _))⟩

/--
lemma `BiTotal.rel_exists` / 引理 `BiTotal.rel_exists`

English:
lemma BiTotal.rel_exists
  given: (h : BiTotal R)
  proof: fun _ _ Hrel =>
    ⟨fun ⟨a, pa⟩ => (h.left a).imp fun _ Rab => (Hrel Rab).1 pa,
      fun ⟨b, qb⟩ => (h.right b).imp fun _ Rab => (Hrel Rab).2 qb⟩

中文:
引理 BiTotal.rel_存在
  条件: (h : BiTotal R)
  证明: fun _ _ Hrel =>
    ⟨fun ⟨a, pa⟩ => (h.left a).imp fun _ Rab => (Hrel Rab).1 pa,
      fun ⟨b, qb⟩ => (h.right b).imp fun _ Rab => (Hrel Rab).2 qb⟩

Depends on / 依赖: h.left, h.right
-/
lemma BiTotal.rel_exists (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => exists i, p i) (fun q => exists i, q i) :=
  fun _ _ Hrel =>
    ⟨fun ⟨a, pa⟩ => (h.left a).imp fun _ Rab => (Hrel Rab).1 pa,
      fun ⟨b, qb⟩ => (h.right b).imp fun _ Rab => (Hrel Rab).2 qb⟩

/--
lemma `left_unique_of_rel_eq` / 引理 `left_unique_of_rel_eq`

English:
lemma left_unique_of_rel_eq
  given: {eq' : β -> β -> Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq')
  statement: LeftUnique R
  proof: fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

中文:
引理 left_unique_of_rel_eq
  条件: {eq' : β -> β -> 命题} (he : (R ⇒ (R ⇒ 当且仅当)) 相等 eq')
  结论: LeftUnique R
  证明: fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)
-/
lemma left_unique_of_rel_eq {eq' : β -> β -> Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

end

/--
lemma `rel_imp` / 引理 `rel_imp`

English:
lemma rel_imp
  statement: (Iff ⇒ (Iff ⇒ Iff)) (· -> ·) (· -> ·)
  proof: fun _ _ h _ _ l => imp_congr h l

中文:
引理 rel_imp
  结论: (当且仅当 ⇒ (当且仅当 ⇒ 当且仅当)) (· -> ·) (· -> ·)
  证明: fun _ _ h _ _ l => imp_congr h l

Depends on / 依赖: imp_congr
-/
lemma rel_imp : (Iff ⇒ (Iff ⇒ Iff)) (· -> ·) (· -> ·) :=
  fun _ _ h _ _ l => imp_congr h l

/--
lemma `rel_not` / 引理 `rel_not`

English:
lemma rel_not
  statement: (Iff ⇒ Iff) Not Not
  proof: fun _ _ h => not_congr h

中文:
引理 rel_not
  结论: (当且仅当 ⇒ 当且仅当) 非 非
  证明: fun _ _ h => not_congr h

Depends on / 依赖: not_congr
-/
lemma rel_not : (Iff ⇒ Iff) Not Not :=
  fun _ _ h => not_congr h

/--
lemma `bi_total_eq` / 引理 `bi_total_eq`

English:
lemma bi_total_eq
  given: {α : Type u₁}
  statement: Relator.BiTotal (@Eq α)
  proof: { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

中文:
引理 bi_total_eq
  条件: {α : 类型u₁}
  结论: Relator.BiTotal (@相等 α)
  证明: { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }
-/
lemma bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

variable {α : Type*} {β : Type*} {γ : Type*}
variable {r : α -> β -> Prop}

/--
lemma `LeftUnique.flip` / 引理 `LeftUnique.flip`

English:
lemma LeftUnique.flip
  given: (h : LeftUnique r)
  statement: RightUnique (flip r)
  proof: fun _ _ _ h₁ h₂ => h h₁ h₂

中文:
引理 LeftUnique.flip
  条件: (h : LeftUnique r)
  结论: RightUnique (flip r)
  证明: fun _ _ _ h₁ h₂ => h h₁ h₂
-/
lemma LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) :=
  fun _ _ _ h₁ h₂ => h h₁ h₂

/--
lemma `rel_and` / 引理 `rel_and`

English:
lemma rel_and
  statement: ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·)
  proof: fun _ _ h₁ _ _ h₂ => and_congr h₁ h₂

中文:
引理 rel_and
  结论: ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·)
  证明: fun _ _ h₁ _ _ h₂ => and_congr h₁ h₂

Depends on / 依赖: and_congr
-/
lemma rel_and : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·) :=
  fun _ _ h₁ _ _ h₂ => and_congr h₁ h₂

/--
lemma `rel_or` / 引理 `rel_or`

English:
lemma rel_or
  statement: ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·)
  proof: fun _ _ h₁ _ _ h₂ => or_congr h₁ h₂

中文:
引理 rel_or
  结论: ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·)
  证明: fun _ _ h₁ _ _ h₂ => or_congr h₁ h₂

Depends on / 依赖: or_congr
-/
lemma rel_or : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·) :=
  fun _ _ h₁ _ _ h₂ => or_congr h₁ h₂

/--
lemma `rel_iff` / 引理 `rel_iff`

English:
lemma rel_iff
  statement: ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·)
  proof: fun _ _ h₁ _ _ h₂ => iff_congr h₁ h₂

中文:
引理 rel_iff
  结论: ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·)
  证明: fun _ _ h₁ _ _ h₂ => iff_congr h₁ h₂

Depends on / 依赖: iff_congr
-/
lemma rel_iff : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·) :=
  fun _ _ h₁ _ _ h₂ => iff_congr h₁ h₂

/--
lemma `rel_eq` / 引理 `rel_eq`

English:
lemma rel_eq
  given: {r : α -> β -> Prop} (hr : BiUnique r)
  statement: (r ⇒ r ⇒ (· ↔ ·)) (· = ·) (· = ·)
  proof: fun _ _ h₁ _ _ h₂ => ⟨fun h => hr.right h₁ h.symm ▸ h₂, fun h => hr.left h₁ h.symm ▸ h₂⟩

中文:
引理 rel_eq
  条件: {r : α -> β -> 命题} (hr : BiUnique r)
  结论: (r ⇒ r ⇒ (· ↔ ·)) (· = ·) (· = ·)
  证明: fun _ _ h₁ _ _ h₂ => ⟨fun h => hr.right h₁ h.symm ▸ h₂, fun h => hr.left h₁ h.symm ▸ h₂⟩

Depends on / 依赖: h.symm, hr.left, hr.right
-/
lemma rel_eq {r : α -> β -> Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (· ↔ ·)) (· = ·) (· = ·) :=
fun _ _ h₁ _ _ h₂ => ⟨fun h => hr.right h₁ h.symm ▸ h₂, fun h => hr.left h₁ h.symm ▸ h₂⟩

open Function

variable {r₁₁ : α -> α -> Prop} {r₁₂ : α -> β -> Prop} {r₂₁ : β -> α -> Prop}
  {r₂₃ : β -> γ -> Prop} {r₁₃ : α -> γ -> Prop}

namespace LeftTotal

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (hr : forall a : α, r₁₁ a a)
  proof: fun a => ⟨a, hr _⟩

中文:
引理 refl
  条件: (hr : 对任意 a : α, r₁₁ a a)
  证明: fun a => ⟨a, hr _⟩
-/
protected lemma refl (hr : forall a : α, r₁₁ a a) :
    LeftTotal r₁₁ :=
  fun a => ⟨a, hr _⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (hr : forall (a : α) (b : β), r₁₂ a b -> r₂₁ b a)
  proof: fun h a => (h a).imp (fun _ => hr _ _)

中文:
引理 symm
  条件: (hr : 对任意 (a : α) (b : β), r₁₂ a b -> r₂₁ b a)
  证明: fun h a => (h a).imp (fun _ => hr _ _)
-/
protected lemma symm (hr : forall (a : α) (b : β), r₁₂ a b -> r₂₁ b a) :
    LeftTotal r₁₂ -> RightTotal r₂₁ :=
  fun h a => (h a).imp (fun _ => hr _ _)

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (hr : forall (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c)
  proof: fun h₁ h₂ a => let ⟨b, hab⟩ := h₁ a; let ⟨c, hbc⟩ := h₂ b; ⟨c, hr _ _ _ hab hbc⟩

中文:
引理 trans
  条件: (hr : 对任意 (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c)
  证明: fun h₁ h₂ a => let ⟨b, hab⟩ := h₁ a; let ⟨c, hbc⟩ := h₂ b; ⟨c, hr _ _ _ hab hbc⟩
-/
protected lemma trans (hr : forall (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c) :
    LeftTotal r₁₂ -> LeftTotal r₂₃ -> LeftTotal r₁₃ :=
  fun h₁ h₂ a => let ⟨b, hab⟩ := h₁ a; let ⟨c, hbc⟩ := h₂ b; ⟨c, hr _ _ _ hab hbc⟩

end LeftTotal

namespace RightTotal

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (hr : forall a : α, r₁₁ a a)
  statement: RightTotal r₁₁
  proof: LeftTotal.refl hr

中文:
引理 refl
  条件: (hr : 对任意 a : α, r₁₁ a a)
  结论: RightTotal r₁₁
  证明: LeftTotal.refl hr
-/
protected lemma refl (hr : forall a : α, r₁₁ a a) : RightTotal r₁₁ :=
  LeftTotal.refl hr

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (hr : forall (a : α) (b : β), r₁₂ a b -> r₂₁ b a)
  proof: LeftTotal.symm (fun _ _ => hr _ _)

中文:
引理 symm
  条件: (hr : 对任意 (a : α) (b : β), r₁₂ a b -> r₂₁ b a)
  证明: LeftTotal.symm (fun _ _ => hr _ _)
-/
protected lemma symm (hr : forall (a : α) (b : β), r₁₂ a b -> r₂₁ b a) :
    RightTotal r₁₂ -> LeftTotal r₂₁ :=
  LeftTotal.symm (fun _ _ => hr _ _)

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (hr : forall (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c)
  proof: swap LeftTotal.trans (fun _ _ _ => swap <| hr _ _ _)

中文:
引理 trans
  条件: (hr : 对任意 (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c)
  证明: swap LeftTotal.trans (fun _ _ _ => swap <| hr _ _ _)
-/
protected lemma trans (hr : forall (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c) :
    RightTotal r₁₂ -> RightTotal r₂₃ -> RightTotal r₁₃ :=
swap LeftTotal.trans (fun _ _ _ => swap <| hr _ _ _)

end RightTotal

namespace BiTotal

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (hr : forall a : α, r₁₁ a a)
  proof: ⟨LeftTotal.refl hr, RightTotal.refl hr⟩

中文:
引理 refl
  条件: (hr : 对任意 a : α, r₁₁ a a)
  证明: ⟨LeftTotal.refl hr, RightTotal.refl hr⟩
-/
protected lemma refl (hr : forall a : α, r₁₁ a a) :
    BiTotal r₁₁ :=
  ⟨LeftTotal.refl hr, RightTotal.refl hr⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (hr : forall (a : α) (b : β), r₁₂ a b -> r₂₁ b a)
  proof: fun h => ⟨h.2.symm hr, h.1.symm hr⟩

中文:
引理 symm
  条件: (hr : 对任意 (a : α) (b : β), r₁₂ a b -> r₂₁ b a)
  证明: fun h => ⟨h.2.symm hr, h.1.symm hr⟩
-/
protected lemma symm (hr : forall (a : α) (b : β), r₁₂ a b -> r₂₁ b a) :
    BiTotal r₁₂ -> BiTotal r₂₁ :=
  fun h => ⟨h.2.symm hr, h.1.symm hr⟩

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (hr : forall (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c)
  proof: fun h₁ h₂ => ⟨h₁.1.trans hr h₂.1, h₁.2.trans hr h₂.2⟩

中文:
引理 trans
  条件: (hr : 对任意 (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c)
  证明: fun h₁ h₂ => ⟨h₁.1.trans hr h₂.1, h₁.2.trans hr h₂.2⟩
-/
protected lemma trans (hr : forall (a : α) (b : β) (c : γ), r₁₂ a b -> r₂₃ b c -> r₁₃ a c) :
    BiTotal r₁₂ -> BiTotal r₂₃ -> BiTotal r₁₃ :=
  fun h₁ h₂ => ⟨h₁.1.trans hr h₂.1, h₁.2.trans hr h₂.2⟩

end BiTotal

end Relator
