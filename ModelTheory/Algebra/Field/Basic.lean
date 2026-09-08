/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Syntax
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The First-Order Theory of Fields

This file defines the first-order theory of fields as a theory over the language of rings.

## Main definitions

- `FirstOrder.Language.Theory.field` : the theory of fields
- `FirstOrder.Model.fieldOfModelField` : a model of the theory of fields on a type `K` that
  already has ring operations.
- `FirstOrder.Model.compatibleRingOfModelField` : shows that the ring operations on `K` given
  by `fieldOfModelField` are compatible with the ring operations on `K` given by the
  `Language.ring.Structure` instance.
-/

@[expose] public section

variable {K : Type*}

namespace FirstOrder

namespace Field

open Language FirstOrder.Ring Structure BoundedFormula

/-- An indexing type to name each of the field axioms. The theory
of fields is defined as the range of a function `FieldAxiom ->
Language.ring.Sentence` -/
/-
**FirstOrder.Field.FieldAxiom** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Field`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An indexing type to name each of the field axioms. The theory
of fields is defined as the range of a function `FieldAxiom ->
Language.ring.Sentence`
-/
inductive FieldAxiom : Type
  | addAssoc : FieldAxiom
  | zeroAdd : FieldAxiom
  | negAddCancel : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | existsInv : FieldAxiom
  | leftDistrib : FieldAxiom
  | existsPairNE : FieldAxiom

/-- The first-order sentence corresponding to each field axiom -/
@[simp]
/-
**FirstOrder.Field.FieldAxiom.toSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.F
ield.FieldAxiom`。
形式化陈述：FirstOrder.Field.FieldAxiom → FirstOrder.Language.ring.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first-order sentence corresponding to each field axiom
-/
def FieldAxiom.toSentence : FieldAxiom → Language.ring.Sentence
  | .addAssoc => ∀' ∀' ∀' (((&0 + &1) + &2) =' (&0 + (&1 + &2)))
  | .zeroAdd => ∀' (((0 : Language.ring.Term _) + &0) =' &0)
  | .negAddCancel => ∀' ∀' ((-&0 + &0) =' 0)
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .mulComm => ∀' ∀' ((&0 * &1) =' (&1 * &0))
  | .oneMul => ∀' (((1 : Language.ring.Term _) * &0) =' &0)
  | .existsInv => ∀' (∼(&0 =' 0) ⟹ ∃' ((&0 * &1) =' 1))
  | .leftDistrib => ∀' ∀' ∀' ((&0 * (&1 + &2)) =' ((&0 * &1) + (&0 * &2)))
  | .existsPairNE => ∃' ∃' (∼(&0 =' &1))

/-- The Proposition corresponding to each field axiom -/
@[simp]
/-
**FirstOrder.Field.FieldAxiom.toProp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Field
.FieldAxiom`。
形式化陈述：(K : Type u_2) → [Add K] → [Mul K] → [Neg K] → [Zero K] → [One K] → FirstO
rder.Field.FieldAxiom → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Proposition corresponding to each field axiom
-/
def FieldAxiom.toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] :
    FieldAxiom → Prop
  | .addAssoc => ∀ x y z : K, (x + y) + z = x + (y + z)
  | .zeroAdd => ∀ x : K, 0 + x = x
  | .negAddCancel => ∀ x : K, -x + x = 0
  | .mulAssoc => ∀ x y z : K, (x * y) * z = x * (y * z)
  | .mulComm => ∀ x y : K, x * y = y * x
  | .oneMul => ∀ x : K, 1 * x = x
  | .existsInv => ∀ x : K, x ≠ 0 → ∃ y, x * y = 1
  | .leftDistrib => ∀ x y z : K, x * (y + z) = x * y + x * z
  | .existsPairNE => ∃ x y : K, x ≠ y

/-- The first-order theory of fields, as a theory over the language of rings -/
/-
**FirstOrder.Field._root_.FirstOrder.Language.Theory.field** 是 Mathlib 中的一个定义，位于
命名空间 `FirstOrder.Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first-order theory of fields, as a theory over the language of rings
-/
def _root_.FirstOrder.Language.Theory.field : Language.ring.Theory :=
  Set.range FieldAxiom.toSentence
/-
**FirstOrder.Field.FieldAxiom.realize_toSentence_iff_toProp** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Field.FieldAxiom`。
形式化陈述：∀ {K : Type u_2} [inst : Add K] [inst_1 : Mul K] [inst_2 : Neg K] [inst_3 
: Zero K] [inst_4 : One K]   [inst_5 : FirstOrder.Ring.CompatibleRing K] (ax : F
irstOrder.Field.FieldAxiom),   K ⊨ ax.toSentence ↔ FirstOrder.Field.FieldAxiom.t
oProp K ax
参数：ax : FirstOrder.Field.FieldAxiom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Ring.realize_add`：realize_add (x y : ring.Term α) (v : α -> R
) : Term.realize v (x + y) = Term.realize v x + Term.realize v y
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `cast.congr_simp`：∀ {α β : Sort u} (h : α = β) (a a_1 : α), a = a_1 → cas
t h a = cast h a_1
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.castPred_one`：castPred_one [NeZero n] : castPred (1 : Fin (n + 2)) (
Fin.ext_iff.not.2 one_lt_last.ne) = 1
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Ring.realize_zero`：realize_zero (v : α -> R) : Term.realize v
 (0 : ring.Term α) = 0
· 使用定理 `FirstOrder.Ring.realize_neg`：realize_neg (x : ring.Term α) (v : α -> R) 
: Term.realize v (-x) = -Term.realize v x
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `FirstOrder.Ring.realize_mul`：realize_mul (x y : ring.Term α) (v : α -> R
) : Term.realize v (x * y) = Term.realize v x * Term.realize v y
· 使用定理 `FirstOrder.Ring.realize_one`：realize_one (v : α -> R) : Term.realize v (
1 : ring.Term α) = 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem FieldAxiom.realize_toSentence_iff_toProp {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    (ax : FieldAxiom) :
    (K ⊨ (ax.toSentence : Sentence Language.ring)) ↔ ax.toProp K := by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]
/-
**FirstOrder.Field.FieldAxiom.toProp_of_model** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Field.FieldAxiom`。
形式化陈述：∀ {K : Type u_2} [inst : Add K] [inst_1 : Mul K] [inst_2 : Neg K] [inst_3 
: Zero K] [inst_4 : One K]   [inst_5 : FirstOrder.Ring.CompatibleRing K] [K ⊨ Fi
rstOrder.Language.Theory.field] (ax : FirstOrder.Field.FieldAxiom),   FirstOrder
.Field.FieldAxiom.toProp K ax
参数：ax : FirstOrder.Field.FieldAxiom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Field.FieldAxiom.realize_toSentence_iff_toProp`：∀ {K : Type u
_2} [inst : Add K] [inst_1 : Mul K] [inst_2 : Neg K] [inst_3 : Zero K] [inst_4 :
 One K]   [inst_5 : FirstOrder.Ring.CompatibleR…
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem FieldAxiom.toProp_of_model {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    [Theory.field.Model K] (ax : FieldAxiom) : ax.toProp K :=
  (FieldAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.field
      (Set.mem_range_self ax))

open FieldAxiom

/-- A model for the theory of fields is a field. To introduced locally on Types that don't
already have instances for ring operations.

When this is used, it is almost always useful to also add locally the instance
`compatibleFieldOfModelField` afterwards. -/
/-
**FirstOrder.Field.fieldOfModelField** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Fie
ld`。
形式化陈述：fieldOfModelField (K : Type*) [Language.ring.Structure K] [Theory.field.Mo
del K] : Field K
参数：K : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A model for the theory of fields is a field. To introduced locally on Types that
 don't
already have instances for ring operations.

When this is used, it is almost always useful to also add locally the instance
`compatibleFieldOfModelField` afterwards.
-/
noncomputable abbrev fieldOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : Field K :=
  letI : DecidableEq K := Classical.decEq K
  letI := addOfRingStructure K
  letI := mulOfRingStructure K
  letI := negOfRingStructure K
  letI := zeroOfRingStructure K
  letI := oneOfRingStructure K
  letI := compatibleRingOfRingStructure K
  have exists_inv : ∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1 :=
    existsInv.toProp_of_model
  letI : Inv K := ⟨fun x => if hx0 : x = 0 then 0 else Classical.choose (exists_inv x hx0)⟩
  Field.ofMinimalAxioms K
    addAssoc.toProp_of_model
    zeroAdd.toProp_of_model
    negAddCancel.toProp_of_model
    mulAssoc.toProp_of_model
    mulComm.toProp_of_model
    oneMul.toProp_of_model
    (fun x hx0 => show x * (dite _ _ _) = _ from
        (dif_neg hx0).symm ▸ Classical.choose_spec (existsInv.toProp_of_model x hx0))
    (dif_pos rfl)
    leftDistrib.toProp_of_model
    existsPairNE.toProp_of_model

section

attribute [local instance] fieldOfModelField

/-- The instances given by `fieldOfModelField` are compatible with the `Language.ring.Structure`
instance on `K`. This instance is to be used on models for the language of fields that do
not already have the ring operations on the Type.

Always add `fieldOfModelField` as a local instance first before using this instance.
-/
/-
**FirstOrder.Field.compatibleRingOfModelField** 是 Mathlib 中的一个缩写定义，位于命名空间 `First
Order.Field`。
形式化陈述：compatibleRingOfModelField (K : Type*) [Language.ring.Structure K] [Theory
.field.Model K] : CompatibleRing K
参数：K : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The instances given by `fieldOfModelField` are compatible with the `Language.rin
g.Structure`
instance on `K`. This instance is to be used on models for the language of field
s that do
not already have the ring operations on the Type.

Always add `fieldOfModelField` as a local instance first before using this insta
nce.
-/
noncomputable abbrev compatibleRingOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : CompatibleRing K :=
  compatibleRingOfRingStructure K

end

/-
**FirstOrder.Field.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] [CompatibleRing K] : Theory.field.Model K :=
  { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)]
      cases a with
      | existsPairNE => exact exists_pair_ne K
      | existsInv => exact fun x hx0 => ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
      | addAssoc => exact add_assoc
      | zeroAdd => exact zero_add
      | negAddCancel => exact neg_add_cancel
      | mulAssoc => exact mul_assoc
      | mulComm => exact mul_comm
      | oneMul => exact one_mul
      | leftDistrib => exact mul_add }

end Field

end FirstOrder

