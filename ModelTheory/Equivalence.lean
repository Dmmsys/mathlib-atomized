/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Satisfiability

/-!
# Equivalence of Formulas

## Main Definitions
- `FirstOrder.Language.Theory.Imp`: `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`.
- `FirstOrder.Language.Theory.Iff`: `φ ⇔[T] ψ` indicates that `φ` and `ψ` are equivalent formulas or
  sentences in models of `T`.

## TODO
- Define the quotient of `L.Formula α` modulo `⇔[T]` and its Boolean Algebra structure.

-/

@[expose] public section

universe u v w w'

open Cardinal CategoryTheory

open FirstOrder

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : Nat}
variable {M : Type*} [Nonempty M] [L.Structure M] [M ⊨ T]

namespace Theory

/--
Definition of `Imp` / `Imp` 的定义

English:
definition Imp
  signature: (T : L.Theory) (φ ψ : L.BoundedFormula α n)
  body: T ⊨ᵇ φ.imp ψ

@[inherit_doc FirstOrder.Language.Theory.Imp]
scoped[FirstOrder] notation:51 φ:50 " ⟹[" T "] " ψ:51 => Language.Theory.Imp T φ ψ

中文:
定义 Imp
  签名: (T : L.Theory) (φ ψ : L.BoundedFormula α n)
  定义体: T ⊨ᵇ φ.imp ψ

@[inherit_doc FirstOrder.Language.Theory.Imp]
scoped[FirstOrder] notation:51 φ:50 " ⟹[" T "] " ψ:51 => Language.Theory.Imp T φ ψ
-/
protected def Imp (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.imp ψ

@[inherit_doc FirstOrder.Language.Theory.Imp]
scoped[FirstOrder] notation:51 φ:50 " ⟹[" T "] " ψ:51 => Language.Theory.Imp T φ ψ

namespace Imp

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (φ : L.BoundedFormula α n)
  statement: φ ⟹[T] φ
  proof: fun _ _ _ => id

中文:
定理 refl
  条件: (φ : L.BoundedFormula α n)
  结论: φ ⟹[T] φ
  证明: fun _ _ _ => id
-/
protected theorem refl (φ : L.BoundedFormula α n) : φ ⟹[T] φ := fun _ _ _ => id

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl (L.BoundedFormula α n) T.Imp
  body: ⟨Imp.refl⟩

@[trans]

中文:
实例 :
  签名: @Std.Refl (L.BoundedFormula α n) T.Imp
  定义体: ⟨Imp.refl⟩

@[trans]

Depends on / 依赖: Imp.refl
-/
instance : @Std.Refl (L.BoundedFormula α n) T.Imp := ⟨Imp.refl⟩

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ)
  proof: fun M v xs => (h2 M v xs) ∘ (h1 M v xs)

中文:
定理 trans
  条件: {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ)
  证明: fun M v xs => (h2 M v xs) ∘ (h1 M v xs)
-/
protected theorem trans {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ) :
    φ ⟹[T] θ := fun M v xs => (h2 M v xs) ∘ (h1 M v xs)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans (L.BoundedFormula α n) T.Imp
  body: ⟨fun _ _ _ => Imp.trans⟩

中文:
实例 :
  签名: 是Trans (L.BoundedFormula α n) T.Imp
  定义体: ⟨fun _ _ _ => Imp.trans⟩

Depends on / 依赖: Imp.trans
-/
instance : IsTrans (L.BoundedFormula α n) T.Imp := ⟨fun _ _ _ => Imp.trans⟩

end Imp

section Imp

/--
lemma `bot_imp` / 引理 `bot_imp`

English:
lemma bot_imp
  given: (φ : L.BoundedFormula α n)
  statement: ⊥ ⟹[T] φ
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot, false_implies]

中文:
引理 bot_imp
  条件: (φ : L.BoundedFormula α n)
  结论: ⊥ ⟹[T] φ
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot, false_implies]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_bot, BoundedFormula.realize_imp, false_implies, realize_bot, realize_imp
-/
lemma bot_imp (φ : L.BoundedFormula α n) : ⊥ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot, false_implies]

/--
lemma `imp_top` / 引理 `imp_top`

English:
lemma imp_top
  given: (φ : L.BoundedFormula α n)
  statement: φ ⟹[T] ⊤
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]

中文:
引理 imp_top
  条件: (φ : L.BoundedFormula α n)
  结论: φ ⟹[T] ⊤
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true, realize_imp, realize_top
-/
lemma imp_top (φ : L.BoundedFormula α n) : φ ⟹[T] ⊤ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]

/--
lemma `imp_sup_left` / 引理 `imp_sup_left`

English:
lemma imp_sup_left
  given: (φ ψ : L.BoundedFormula α n)
  statement: φ ⟹[T] φ ⊔ ψ
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inl

中文:
引理 imp_sup_left
  条件: (φ ψ : L.BoundedFormula α n)
  结论: φ ⟹[T] φ ⊔ ψ
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inl

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_sup, Or.inl, realize_imp, realize_sup
-/
lemma imp_sup_left (φ ψ : L.BoundedFormula α n) : φ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inl

/--
lemma `imp_sup_right` / 引理 `imp_sup_right`

English:
lemma imp_sup_right
  given: (φ ψ : L.BoundedFormula α n)
  statement: ψ ⟹[T] φ ⊔ ψ
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inr

中文:
引理 imp_sup_right
  条件: (φ ψ : L.BoundedFormula α n)
  结论: ψ ⟹[T] φ ⊔ ψ
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inr

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_sup, Or.inr, realize_imp, realize_sup
-/
lemma imp_sup_right (φ ψ : L.BoundedFormula α n) : ψ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inr

/--
lemma `sup_imp` / 引理 `sup_imp`

English:
lemma sup_imp
  given: {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ)
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact fun h => h.elim (h₁ M v xs) (h₂ M v xs)

中文:
引理 sup_imp
  条件: {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ)
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact fun h => h.elim (h₁ M v xs) (h₂ M v xs)

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_sup, h.elim, realize_imp, realize_sup
-/
lemma sup_imp {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ) :
    φ ⊔ ψ ⟹[T] θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact fun h => h.elim (h₁ M v xs) (h₂ M v xs)

/--
lemma `sup_imp_iff` / 引理 `sup_imp_iff`

English:
lemma sup_imp_iff
  given: {φ ψ θ : L.BoundedFormula α n}
  proof: ⟨fun h => ⟨(imp_sup_left _ _).trans h, (imp_sup_right _ _).trans h⟩,
    fun ⟨h₁, h₂⟩ => sup_imp h₁ h₂⟩

中文:
引理 sup_imp_iff
  条件: {φ ψ θ : L.BoundedFormula α n}
  证明: ⟨fun h => ⟨(imp_sup_left _ _).trans h, (imp_sup_right _ _).trans h⟩,
    fun ⟨h₁, h₂⟩ => sup_imp h₁ h₂⟩

Depends on / 依赖: imp_sup_left, imp_sup_right, sup_imp
-/
lemma sup_imp_iff {φ ψ θ : L.BoundedFormula α n} :
    (φ ⊔ ψ ⟹[T] θ) ↔ (φ ⟹[T] θ) ∧ (ψ ⟹[T] θ) :=
  ⟨fun h => ⟨(imp_sup_left _ _).trans h, (imp_sup_right _ _).trans h⟩,
    fun ⟨h₁, h₂⟩ => sup_imp h₁ h₂⟩

/--
lemma `inf_imp_left` / 引理 `inf_imp_left`

English:
lemma inf_imp_left
  given: (φ ψ : L.BoundedFormula α n)
  statement: φ ⊓ ψ ⟹[T] φ
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.left

中文:
引理 inf_imp_left
  条件: (φ ψ : L.BoundedFormula α n)
  结论: φ ⊓ ψ ⟹[T] φ
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.left

Depends on / 依赖: And.left, BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_inf, realize_imp, realize_inf
-/
lemma inf_imp_left (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.left

/--
lemma `inf_imp_right` / 引理 `inf_imp_right`

English:
lemma inf_imp_right
  given: (φ ψ : L.BoundedFormula α n)
  statement: φ ⊓ ψ ⟹[T] ψ
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.right

中文:
引理 inf_imp_right
  条件: (φ ψ : L.BoundedFormula α n)
  结论: φ ⊓ ψ ⟹[T] ψ
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.right

Depends on / 依赖: And.right, BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_inf, realize_imp, realize_inf
-/
lemma inf_imp_right (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.right

/--
lemma `imp_inf` / 引理 `imp_inf`

English:
lemma imp_inf
  given: {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ)
  proof: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact fun h => ⟨h₁ M v xs h, h₂ M v xs h⟩

中文:
引理 imp_inf
  条件: {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ)
  证明: fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact fun h => ⟨h₁ M v xs h, h₂ M v xs h⟩

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_imp, BoundedFormula.realize_inf, realize_imp, realize_inf
-/
lemma imp_inf {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ) :
    φ ⟹[T] ψ ⊓ θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact fun h => ⟨h₁ M v xs h, h₂ M v xs h⟩

/--
lemma `imp_inf_iff` / 引理 `imp_inf_iff`

English:
lemma imp_inf_iff
  given: {φ ψ θ : L.BoundedFormula α n}
  proof: ⟨fun h => ⟨h.trans (inf_imp_left _ _), h.trans (inf_imp_right _ _)⟩,
    fun ⟨h₁, h₂⟩ => imp_inf h₁ h₂⟩

中文:
引理 imp_inf_iff
  条件: {φ ψ θ : L.BoundedFormula α n}
  证明: ⟨fun h => ⟨h.trans (inf_imp_left _ _), h.trans (inf_imp_right _ _)⟩,
    fun ⟨h₁, h₂⟩ => imp_inf h₁ h₂⟩

Depends on / 依赖: h.trans, imp_inf, inf_imp_left, inf_imp_right
-/
lemma imp_inf_iff {φ ψ θ : L.BoundedFormula α n} :
    (φ ⟹[T] ψ ⊓ θ) ↔ (φ ⟹[T] ψ) ∧ (φ ⟹[T] θ) :=
  ⟨fun h => ⟨h.trans (inf_imp_left _ _), h.trans (inf_imp_right _ _)⟩,
    fun ⟨h₁, h₂⟩ => imp_inf h₁ h₂⟩

end Imp

/--
Definition of `Iff` / `Iff` 的定义

English:
definition Iff
  signature: (T : L.Theory) (φ ψ : L.BoundedFormula α n)
  body: T ⊨ᵇ φ.iff ψ

@[inherit_doc FirstOrder.Language.Theory.Iff]
scoped[FirstOrder]
notation:51 φ:50 " ⇔[" T "] " ψ:51 => Language.Theory.Iff T φ ψ

中文:
定义 当且仅当
  签名: (T : L.Theory) (φ ψ : L.BoundedFormula α n)
  定义体: T ⊨ᵇ φ.iff ψ

@[inherit_doc FirstOrder.Language.Theory.Iff]
scoped[FirstOrder]
notation:51 φ:50 " ⇔[" T "] " ψ:51 => Language.Theory.Iff T φ ψ
-/
protected def Iff (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.iff ψ

@[inherit_doc FirstOrder.Language.Theory.Iff]
scoped[FirstOrder]
notation:51 φ:50 " ⇔[" T "] " ψ:51 => Language.Theory.Iff T φ ψ

/--
theorem `iff_iff_imp_and_imp` / 定理 `iff_iff_imp_and_imp`

English:
theorem iff_iff_imp_and_imp
  given: {φ ψ : L.BoundedFormula α n}
  proof: by
  simp only [Theory.Imp, ModelsBoundedFormula, BoundedFormula.realize_imp, ← forall_and,
    Theory.Iff, BoundedFormula.realize_iff, iff_iff_implies_and_implies]

中文:
定理 iff_iff_imp_and_imp
  条件: {φ ψ : L.BoundedFormula α n}
  证明: by
  simp only [Theory.Imp, ModelsBoundedFormula, BoundedFormula.realize_imp, ← forall_and,
    Theory.Iff, BoundedFormula.realize_iff, iff_iff_implies_and_implies]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_iff, BoundedFormula.realize_imp, ModelsBoundedFormula, Theory, Theory.Iff, Theory.Imp, forall_and, iff_iff_implies_and_implies, realize_iff, realize_imp
-/
theorem iff_iff_imp_and_imp {φ ψ : L.BoundedFormula α n} :
    (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ) := by
  simp only [Theory.Imp, ModelsBoundedFormula, BoundedFormula.realize_imp, ← forall_and,
    Theory.Iff, BoundedFormula.realize_iff, iff_iff_implies_and_implies]

/--
theorem `imp_antisymm` / 定理 `imp_antisymm`

English:
theorem imp_antisymm
  given: {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ)
  proof: iff_iff_imp_and_imp.2 ⟨h₁, h₂⟩

中文:
定理 imp_antisymm
  条件: {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ)
  证明: iff_iff_imp_and_imp.2 ⟨h₁, h₂⟩

Depends on / 依赖: iff_iff_imp_and_imp
-/
theorem imp_antisymm {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ) :
    φ ⇔[T] ψ :=
  iff_iff_imp_and_imp.2 ⟨h₁, h₂⟩

namespace Iff

/--
theorem `mp` / 定理 `mp`

English:
theorem mp
  given: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  proof: (iff_iff_imp_and_imp.1 h).1

中文:
定理 mp
  条件: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  证明: (iff_iff_imp_and_imp.1 h).1
-/
protected theorem mp {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ ⟹[T] ψ := (iff_iff_imp_and_imp.1 h).1

/--
theorem `mpr` / 定理 `mpr`

English:
theorem mpr
  given: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  proof: (iff_iff_imp_and_imp.1 h).2

@[refl]

中文:
定理 mpr
  条件: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  证明: (iff_iff_imp_and_imp.1 h).2

@[refl]
-/
protected theorem mpr {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    ψ ⟹[T] φ := (iff_iff_imp_and_imp.1 h).2

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (φ : L.BoundedFormula α n)
  statement: φ ⇔[T] φ
  proof: fun M v xs => by rw [BoundedFormula.realize_iff]

中文:
定理 refl
  条件: (φ : L.BoundedFormula α n)
  结论: φ ⇔[T] φ
  证明: fun M v xs => by rw [BoundedFormula.realize_iff]
-/
protected theorem refl (φ : L.BoundedFormula α n) : φ ⇔[T] φ :=
  fun M v xs => by rw [BoundedFormula.realize_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl (L.BoundedFormula α n) T.Iff
  body: ⟨Iff.refl⟩

@[symm]

中文:
实例 :
  签名: @Std.Refl (L.BoundedFormula α n) T.当且仅当
  定义体: ⟨Iff.refl⟩

@[symm]

Depends on / 依赖: Iff.refl
-/
instance : @Std.Refl (L.BoundedFormula α n) T.Iff :=
  ⟨Iff.refl⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  statement: {φ ψ : L.BoundedFormula α n}
  proof: fun M v xs => by
  rw [BoundedFormula.realize_iff]; rw [Iff.comm]; rw [← BoundedFormula.realize_iff]
  exact h M v xs

中文:
定理 symm
  结论: {φ ψ : L.BoundedFormula α n}
  证明: fun M v xs => by
  rw [BoundedFormula.realize_iff]; rw [Iff.comm]; rw [← BoundedFormula.realize_iff]
  exact h M v xs
-/
protected theorem symm {φ ψ : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) : ψ ⇔[T] φ := fun M v xs => by
  rw [BoundedFormula.realize_iff]; rw [Iff.comm]; rw [← BoundedFormula.realize_iff]
  exact h M v xs

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (α := L.BoundedFormula α n) T.Iff
  body: ⟨fun _ _ => Iff.symm⟩

@[trans]

中文:
实例 :
  签名: Std.Symm (α := L.BoundedFormula α n) T.当且仅当
  定义体: ⟨fun _ _ => Iff.symm⟩

@[trans]

Depends on / 依赖: BoundedFormula, L.BoundedFormula, T.Iff
-/
instance : Std.Symm (α := L.BoundedFormula α n) T.Iff :=
  ⟨fun _ _ => Iff.symm⟩

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: {φ ψ θ : L.BoundedFormula α n}
  proof: fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩

中文:
定理 trans
  结论: {φ ψ θ : L.BoundedFormula α n}
  证明: fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩
-/
protected theorem trans {φ ψ θ : L.BoundedFormula α n}
    (h1 : φ ⇔[T] ψ) (h2 : ψ ⇔[T] θ) :
    φ ⇔[T] θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans (L.BoundedFormula α n) T.Iff
  body: ⟨fun _ _ _ => Iff.trans⟩

中文:
实例 :
  签名: 是Trans (L.BoundedFormula α n) T.当且仅当
  定义体: ⟨fun _ _ _ => Iff.trans⟩

Depends on / 依赖: Iff.trans
-/
instance : IsTrans (L.BoundedFormula α n) T.Iff :=
  ⟨fun _ _ _ => Iff.trans⟩

/--
theorem `realize_bd_iff` / 定理 `realize_bd_iff`

English:
theorem realize_bd_iff
  statement: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  proof: BoundedFormula.realize_iff.1 (h.realize_boundedFormula M)

中文:
定理 realize_bd_iff
  结论: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  证明: BoundedFormula.realize_iff.1 (h.realize_boundedFormula M)

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_iff, h.realize_boundedFormula, realize_boundedFormula, realize_iff
-/
theorem realize_bd_iff {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
    {v : α -> M} {xs : Fin n -> M} : φ.Realize v xs ↔ ψ.Realize v xs :=
  BoundedFormula.realize_iff.1 (h.realize_boundedFormula M)

/--
theorem `realize_iff` / 定理 `realize_iff`

English:
theorem realize_iff
  statement: {φ ψ : L.Formula α} {M : Type*} [Nonempty M]
  proof: h.realize_bd_iff

中文:
定理 realize_iff
  结论: {φ ψ : L.公式 α} {M : 类型} [非空 M]
  证明: h.realize_bd_iff

Depends on / 依赖: h.realize_bd_iff, realize_bd_iff
-/
theorem realize_iff {φ ψ : L.Formula α} {M : Type*} [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) {v : α -> M} :
    φ.Realize v ↔ ψ.Realize v :=
  h.realize_bd_iff

/--
theorem `models_sentence_iff` / 定理 `models_sentence_iff`

English:
theorem models_sentence_iff
  statement: {φ ψ : L.Sentence} {M : Type*} [Nonempty M]
  proof: h.realize_iff

中文:
定理 models_sentence_iff
  结论: {φ ψ : L.Sentence} {M : 类型} [非空 M]
  证明: h.realize_iff

Depends on / 依赖: h.realize_iff, realize_iff
-/
theorem models_sentence_iff {φ ψ : L.Sentence} {M : Type*} [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) :
    M ⊨ φ ↔ M ⊨ ψ :=
  h.realize_iff

/--
theorem `all` / 定理 `all`

English:
theorem all
  statement: {φ ψ : L.BoundedFormula α (n + 1)}
  proof: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff

中文:
定理 all
  结论: {φ ψ : L.BoundedFormula α (n + 1)}
  证明: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff
-/
protected theorem all {φ ψ : L.BoundedFormula α (n + 1)}
    (h : φ ⇔[T] ψ) : φ.all ⇔[T] ψ.all := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff

/--
theorem `ex` / 定理 `ex`

English:
theorem ex
  given: {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ⇔[T] ψ)
  proof: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff

中文:
定理 ex
  条件: {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ⇔[T] ψ)
  证明: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff
-/
protected theorem ex {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ⇔[T] ψ) :
    φ.ex ⇔[T] ψ.ex := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff

/--
theorem `not` / 定理 `not`

English:
theorem not
  given: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  proof: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff

中文:
定理 not
  条件: {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
  证明: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff
-/
protected theorem not {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ.not ⇔[T] ψ.not := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff

/--
theorem `imp` / 定理 `imp`

English:
theorem imp
  given: {φ ψ φ' ψ' : L.BoundedFormula α n} (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ')
  proof: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

中文:
定理 imp
  条件: {φ ψ φ' ψ' : L.BoundedFormula α n} (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ')
  证明: by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff
-/
protected theorem imp {φ ψ φ' ψ' : L.BoundedFormula α n} (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ.imp φ') ⇔[T] (ψ.imp ψ') := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

end Iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
@[instance_reducible]
/--
Definition of `iffSetoid` / `iffSetoid` 的定义

English:
definition iffSetoid
  signature: (T : L.Theory)
  body: T.Iff
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

中文:
定义 iffSetoid
  签名: (T : L.Theory)
  定义体: T.Iff
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

Depends on / 依赖: T.Iff
-/
def iffSetoid (T : L.Theory) : Setoid (L.BoundedFormula α n) where
  r := T.Iff
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

end Theory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

/--
theorem `iff_not_not` / 定理 `iff_not_not`

English:
theorem iff_not_not
  statement: φ ⇔[T] φ.not.not
  proof: fun M v xs => by
  simp

中文:
定理 iff_not_not
  结论: φ ⇔[T] φ.not.not
  证明: fun M v xs => by
  simp
-/
theorem iff_not_not : φ ⇔[T] φ.not.not := fun M v xs => by
  simp

/--
theorem `imp_iff_not_sup` / 定理 `imp_iff_not_sup`

English:
theorem imp_iff_not_sup
  statement: (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ)
  proof: fun M v xs => by simp [imp_iff_not_or]

中文:
定理 imp_iff_not_sup
  结论: (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ)
  证明: fun M v xs => by simp [imp_iff_not_or]

Depends on / 依赖: imp_iff_not_or
-/
theorem imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  fun M v xs => by simp [imp_iff_not_or]

/--
theorem `sup_iff_not_inf_not` / 定理 `sup_iff_not_inf_not`

English:
theorem sup_iff_not_inf_not
  statement: (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
  proof: fun M v xs => by simp [imp_iff_not_or]

中文:
定理 sup_iff_not_inf_not
  结论: (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
  证明: fun M v xs => by simp [imp_iff_not_or]

Depends on / 依赖: imp_iff_not_or
-/
theorem sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  fun M v xs => by simp [imp_iff_not_or]

/--
theorem `inf_iff_not_sup_not` / 定理 `inf_iff_not_sup_not`

English:
theorem inf_iff_not_sup_not
  statement: (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
  proof: fun M v xs => by simp

中文:
定理 inf_iff_not_sup_not
  结论: (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
  证明: fun M v xs => by simp
-/
theorem inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  fun M v xs => by simp

/--
theorem `all_iff_not_ex_not` / 定理 `all_iff_not_ex_not`

English:
theorem all_iff_not_ex_not
  given: (φ : L.BoundedFormula α (n + 1))
  proof: fun M v xs => by simp

中文:
定理 all_iff_not_ex_not
  条件: (φ : L.BoundedFormula α (n + 1))
  证明: fun M v xs => by simp
-/
theorem all_iff_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    φ.all ⇔[T] φ.not.ex.not := fun M v xs => by simp

/--
theorem `ex_iff_not_all_not` / 定理 `ex_iff_not_all_not`

English:
theorem ex_iff_not_all_not
  given: (φ : L.BoundedFormula α (n + 1))
  proof: fun M v xs => by simp

中文:
定理 ex_iff_not_all_not
  条件: (φ : L.BoundedFormula α (n + 1))
  证明: fun M v xs => by simp
-/
theorem ex_iff_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    φ.ex ⇔[T] φ.not.all.not := fun M v xs => by simp

/--
theorem `iff_all_liftAt` / 定理 `iff_all_liftAt`

English:
theorem iff_all_liftAt
  statement: φ ⇔[T] (φ.liftAt 1 n).all
  proof: fun M v xs => by
  rw [realize_iff]; rw [realize_all_liftAt_one_self]

中文:
定理 iff_all_liftAt
  结论: φ ⇔[T] (φ.liftAt 1 n).all
  证明: fun M v xs => by
  rw [realize_iff]; rw [realize_all_liftAt_one_self]

Depends on / 依赖: realize_all_liftAt_one_self, realize_iff
-/
theorem iff_all_liftAt : φ ⇔[T] (φ.liftAt 1 n).all :=
  fun M v xs => by
  rw [realize_iff]; rw [realize_all_liftAt_one_self]

/--
lemma `inf_not_iff_bot` / 引理 `inf_not_iff_bot`

English:
lemma inf_not_iff_bot
  proof: fun M v xs => by
  simp only [realize_iff, realize_inf, realize_not, and_not_self, realize_bot]

中文:
引理 inf_not_iff_bot
  证明: fun M v xs => by
  simp only [realize_iff, realize_inf, realize_not, and_not_self, realize_bot]

Depends on / 依赖: and_not_self, realize_bot, realize_iff, realize_inf, realize_not
-/
lemma inf_not_iff_bot :
    φ ⊓ ∼φ ⇔[T] ⊥ := fun M v xs => by
  simp only [realize_iff, realize_inf, realize_not, and_not_self, realize_bot]

/--
lemma `sup_not_iff_top` / 引理 `sup_not_iff_top`

English:
lemma sup_not_iff_top
  proof: fun M v xs => by
  simp only [realize_iff, realize_sup, realize_not, realize_top, or_not]

中文:
引理 sup_not_iff_top
  证明: fun M v xs => by
  simp only [realize_iff, realize_sup, realize_not, realize_top, or_not]

Depends on / 依赖: or_not, realize_iff, realize_not, realize_sup, realize_top
-/
lemma sup_not_iff_top :
    φ ⊔ ∼φ ⇔[T] ⊤ := fun M v xs => by
  simp only [realize_iff, realize_sup, realize_not, realize_top, or_not]

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

/--
theorem `iff_not_not` / 定理 `iff_not_not`

English:
theorem iff_not_not
  statement: φ ⇔[T] φ.not.not
  proof: BoundedFormula.iff_not_not φ

中文:
定理 iff_not_not
  结论: φ ⇔[T] φ.not.not
  证明: BoundedFormula.iff_not_not φ

Depends on / 依赖: BoundedFormula, BoundedFormula.iff_not_not, iff_not_not
-/
theorem iff_not_not : φ ⇔[T] φ.not.not :=
  BoundedFormula.iff_not_not φ

/--
theorem `imp_iff_not_sup` / 定理 `imp_iff_not_sup`

English:
theorem imp_iff_not_sup
  statement: (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ)
  proof: BoundedFormula.imp_iff_not_sup φ ψ

中文:
定理 imp_iff_not_sup
  结论: (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ)
  证明: BoundedFormula.imp_iff_not_sup φ ψ

Depends on / 依赖: BoundedFormula, BoundedFormula.imp_iff_not_sup, imp_iff_not_sup
-/
theorem imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  BoundedFormula.imp_iff_not_sup φ ψ

/--
theorem `sup_iff_not_inf_not` / 定理 `sup_iff_not_inf_not`

English:
theorem sup_iff_not_inf_not
  statement: (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
  proof: BoundedFormula.sup_iff_not_inf_not φ ψ

中文:
定理 sup_iff_not_inf_not
  结论: (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
  证明: BoundedFormula.sup_iff_not_inf_not φ ψ

Depends on / 依赖: BoundedFormula, BoundedFormula.sup_iff_not_inf_not, sup_iff_not_inf_not
-/
theorem sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  BoundedFormula.sup_iff_not_inf_not φ ψ

/--
theorem `inf_iff_not_sup_not` / 定理 `inf_iff_not_sup_not`

English:
theorem inf_iff_not_sup_not
  statement: (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
  proof: BoundedFormula.inf_iff_not_sup_not φ ψ

中文:
定理 inf_iff_not_sup_not
  结论: (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
  证明: BoundedFormula.inf_iff_not_sup_not φ ψ

Depends on / 依赖: BoundedFormula, BoundedFormula.inf_iff_not_sup_not, inf_iff_not_sup_not
-/
theorem inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  BoundedFormula.inf_iff_not_sup_not φ ψ

end Formula

end Language

end FirstOrder
