/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic

/-!
# Type synonyms

This file provides two type synonyms for order theory:

* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.
* `Colex α`: Type synonym of `α` to equip it with its colexicographic order. The precise meaning
  depends on the type we take the colex of. Examples include `Finset`, `DFinsupp`, `Finsupp`.

## Notation

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:

* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.
* `Colex`: `toColex : α → Colex α` and `ofColex : Colex α → α`.

## See also

This file is similar to `Mathlib.Algebra.Group.TypeTags.Basic`.
-/

@[expose] public section

assert_not_exists OrderDual

variable {α : Type*}

/-! ### Lexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
/-
**Lex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lex (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym to equip a type with its lexicographic order.
-/
def Lex (α : Type*) :=
  α

/-- `toLex` is the identity function to the `Lex` of a type. -/
@[match_pattern]
/-
**toLex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toLex : α ≃ Lex α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toLex` is the identity function to the `Lex` of a type.
-/
def toLex : α ≃ Lex α :=
  Equiv.refl _

/-- `ofLex` is the identity function from the `Lex` of a type. -/
@[match_pattern]
/-
**ofLex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofLex : Lex α ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofLex` is the identity function from the `Lex` of a type.
-/
def ofLex : Lex α ≃ α :=
  Equiv.refl _

@[simp]
/-
**toLex_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_symm_eq : (@toLex α).symm = ofLex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toLex_symm_eq : (@toLex α).symm = ofLex :=
  rfl

@[simp]
/-
**ofLex_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_symm_eq : (@ofLex α).symm = toLex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofLex_symm_eq : (@ofLex α).symm = toLex :=
  rfl

@[simp]
/-
**toLex_ofLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_ofLex (a : Lex α) : toLex (ofLex a) = a
参数：a : Lex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_ofLex (a : Lex α) : toLex (ofLex a) = a :=
  rfl

@[simp]
/-
**ofLex_toLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_toLex (a : α) : ofLex (toLex a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_toLex (a : α) : ofLex (toLex a) = a :=
  rfl
/-
**toLex_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_inj {a b : α} : toLex a = toLex b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toLex_inj {a b : α} : toLex a = toLex b ↔ a = b := by simp
/-
**ofLex_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofLex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [BEq α] : BEq (Lex α) where
  beq a b := ofLex a == ofLex b
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Lex α) := inferInstanceAs <| LawfulBEq α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [DecidableEq α] : DecidableEq (Lex α) := inferInstanceAs <| DecidableEq α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Inhabited α] : Inhabited (Lex α) := inferInstanceAs <| Inhabited α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Nonempty α] : Nonempty (Lex α) := inferInstanceAs <| Nonempty α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Nontrivial α] : Nontrivial (Lex α) := inferInstanceAs <| Nontrivial α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Unique α] : Unique (Lex α) := inferInstanceAs <| Unique α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α γ} [H : CoeFun α γ] : CoeFun (Lex α) γ where
  coe f := H.coe (ofLex f)

/-- A recursor for `Lex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**Lex.rec** 是 Mathlib 中的一个定义，位于命名空间 `Lex`。
形式化陈述：{α : Type u_1} → {β : Lex α → Sort u_2} → ((a : α) → β (toLex a)) → (a : L
ex α) → β a
参数：(a : α) → β (toLex a)；a : Lex α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `Lex`. Use as `induction x`.
-/
protected def Lex.rec {β : Lex α → Sort*} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)
/-
**Lex.forall** 是 Mathlib 中的一个定理，位于命名空间 `Lex`。
形式化陈述：∀ {α : Type u_1} {p : Lex α → Prop}, (∀ (a : Lex α), p a) ↔ ∀ (a : α), p (
toLex a)
参数：∀ (a : Lex α), p a；a : α；toLex a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma Lex.forall {p : Lex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLex a) := Iff.rfl
/-
**Lex.exists** 是 Mathlib 中的一个定理，位于命名空间 `Lex`。
形式化陈述：∀ {α : Type u_1} {p : Lex α → Prop}, (∃ a, p a) ↔ ∃ a, p (toLex a)
参数：∃ a, p a；toLex a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma Lex.exists {p : Lex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLex a) := Iff.rfl

/-! ### Colexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
/-
**Colex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Colex (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym to equip a type with its lexicographic order.
-/
def Colex (α : Type*) :=
  α

/-- `toColex` is the identity function to the `Colex` of a type. -/
@[match_pattern]
/-
**toColex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toColex : α ≃ Colex α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toColex` is the identity function to the `Colex` of a type.
-/
def toColex : α ≃ Colex α :=
  Equiv.refl _

/-- `ofColex` is the identity function from the `Colex` of a type. -/
@[match_pattern]
/-
**ofColex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofColex : Colex α ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofColex` is the identity function from the `Colex` of a type.
-/
def ofColex : Colex α ≃ α :=
  Equiv.refl _

@[simp]
/-
**toColex_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_symm_eq : (@toColex α).symm = ofColex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toColex_symm_eq : (@toColex α).symm = ofColex :=
  rfl

@[simp]
/-
**ofColex_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_symm_eq : (@ofColex α).symm = toColex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofColex_symm_eq : (@ofColex α).symm = toColex :=
  rfl

@[simp]
/-
**toColex_ofColex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_ofColex (a : Colex α) : toColex (ofColex a) = a
参数：a : Colex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toColex_ofColex (a : Colex α) : toColex (ofColex a) = a :=
  rfl

@[simp]
/-
**ofColex_toColex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_toColex (a : α) : ofColex (toColex a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofColex_toColex (a : α) : ofColex (toColex a) = a :=
  rfl
/-
**toColex_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_inj {a b : α} : toColex a = toColex b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toColex_inj {a b : α} : toColex a = toColex b ↔ a = b := by simp
/-
**ofColex_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_inj {a b : Colex α} : ofColex a = ofColex b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofColex_inj {a b : Colex α} : ofColex a = ofColex b ↔ a = b := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [BEq α] : BEq (Colex α) where
  beq a b := ofColex a == ofColex b
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Colex α) := inferInstanceAs <| LawfulBEq α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [DecidableEq α] : DecidableEq (Colex α) := inferInstanceAs <| DecidableEq α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Inhabited α] : Inhabited (Colex α) := inferInstanceAs <| Inhabited α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Nonempty α] : Nonempty (Colex α) := inferInstanceAs <| Nonempty α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Nontrivial α] : Nontrivial (Colex α) := inferInstanceAs <| Nontrivial α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Unique α] : Unique (Colex α) := inferInstanceAs <| Unique α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α γ} [H : CoeFun α γ] : CoeFun (Colex α) γ where
  coe f := H.coe (ofColex f)

/-- A recursor for `Colex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**Colex.rec** 是 Mathlib 中的一个定义，位于命名空间 `Colex`。
形式化陈述：{α : Type u_1} → {β : Colex α → Sort u_2} → ((a : α) → β (toColex a)) → (a
 : Colex α) → β a
参数：(a : α) → β (toColex a)；a : Colex α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `Colex`. Use as `induction x`.
-/
protected def Colex.rec {β : Colex α → Sort*} (h : ∀ a, β (toColex a)) : ∀ a, β a :=
  fun a => h (ofColex a)
/-
**Colex.forall** 是 Mathlib 中的一个定理，位于命名空间 `Colex`。
形式化陈述：∀ {α : Type u_1} {p : Colex α → Prop}, (∀ (a : Colex α), p a) ↔ ∀ (a : α),
 p (toColex a)
参数：∀ (a : Colex α), p a；a : α；toColex a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma Colex.forall {p : Colex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toColex a) := Iff.rfl
/-
**Colex.exists** 是 Mathlib 中的一个定理，位于命名空间 `Colex`。
形式化陈述：∀ {α : Type u_1} {p : Colex α → Prop}, (∃ a, p a) ↔ ∃ a, p (toColex a)
参数：∃ a, p a；toColex a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma Colex.exists {p : Colex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toColex a) := Iff.rfl
