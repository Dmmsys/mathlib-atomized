/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# Complementary embeddings

Given two embeddings `e₁ : c₁.Embedding c` and `e₂ : c₂.Embedding c`
of complex shapes, we introduce a property `e₁.AreComplementary e₂`
saying that the image subsets of the indices of `c₁` and `c₂` form
a partition of the indices of `c`.

If `e₁.IsTruncLE` and `e₂.IsTruncGE`, and `K : HomologicalComplex C c`,
we construct a quasi-isomorphism `shortComplexTruncLEX₃ToTruncGE` between
the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁ ⟶ K` and `K.truncGE e₂`.

-/

@[expose] public section

open CategoryTheory Limits

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace ComplexShape

namespace Embedding

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

/-- Two embedding `e₁` and `e₂` into a complex shape `c : ComplexShape ι`
are complementary when the range of `e₁.f` and `e₂.f` form a partition of `ι`. -/
/-
**ComplexShape.Embedding.AreComplementary** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexSh
ape.Embedding`。
形式化陈述：{ι : Type u_1} →   {ι₁ : Type u_2} →     {ι₂ : Type u_3} →       {c : Comp
lexShape ι} → {c₁ : ComplexShape ι₁} → {c₂ : ComplexShape ι₂} → c₁.Embedding c →
 c₂.Embedding c → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two embedding `e₁` and `e₂` into a complex shape `c : ComplexShape ι`
are complementary when the range of `e₁.f` and `e₂.f` form a partition of `ι`.
-/
structure AreComplementary : Prop where
  disjoint (i₁ : ι₁) (i₂ : ι₂) : e₁.f i₁ ≠ e₂.f i₂
  union (i : ι) : (∃ i₁, e₁.f i₁ = i) ∨ ∃ i₂, e₂.f i₂ = i

variable {e₁ e₂}

namespace AreComplementary

variable (ac : AreComplementary e₁ e₂)

include ac
/-
**ComplexShape.Embedding.AreComplementary.symm** 是 Mathlib 中的一个引理，位于命名空间 `Comple
xShape.Embedding.AreComplementary`。
形式化陈述：symm : AreComplementary e₂ e₁ where disjoint i₂ i₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ComplexShape.Embedding.AreComplementary.disjoint`：∀ {ι : Type u_1} {ι₁ :
 Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Com
plexShape ι₂}   {e₁ : c₁.Embedding c} …
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `ComplexShape.Embedding.AreComplementary.union`：∀ {ι : Type u_1} {ι₁ : Ty
pe u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Comple
xShape ι₂}   {e₁ : c₁.Embedding c} …
-/
lemma symm : AreComplementary e₂ e₁ where
  disjoint i₂ i₁ := (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm
/-
**ComplexShape.Embedding.AreComplementary.exists_i** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplexShape.Embedding.AreComplementary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_i₁ (i : ι) (hi : ∀ i₂, e₂.f i₂ ≠ i) :
    ∃ i₁, i = e₁.f i₁ := by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl
/-
**ComplexShape.Embedding.AreComplementary.exists_i** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplexShape.Embedding.AreComplementary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_i₂ (i : ι) (hi : ∀ i₁, e₁.f i₁ ≠ i) :
    ∃ i₂, i = e₂.f i₂ :=
  ac.symm.exists_i₁ i hi

variable (e₁ e₂) in
/-- Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious map `ι₁ ⊕ ι₂ → ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`. -/
@[simp]
/-
**ComplexShape.Embedding.AreComplementary.fromSum** 是 Mathlib 中的一个定义，位于命名空间 `Com
plexShape.Embedding.AreComplementary`。
形式化陈述：{ι : Type u_1} →   {ι₁ : Type u_2} →     {ι₂ : Type u_3} →       {c : Comp
lexShape ι} →         {c₁ : ComplexShape ι₁} → {c₂ : ComplexShape ι₂} → c₁.Embed
ding c → c₂.Embedding c → ι₁ ⊕ ι₂ → ι
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious map `ι₁ ⊕ ι₂ → ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`.
-/
def fromSum : ι₁ ⊕ ι₂ → ι
  | Sum.inl i₁ => e₁.f i₁
  | Sum.inr i₂ => e₂.f i₂
/-
**ComplexShape.Embedding.AreComplementary.fromSum_bijective** 是 Mathlib 中的一个引理，位
于命名空间 `ComplexShape.Embedding.AreComplementary`。
形式化陈述：fromSum_bijective : Function.Bijective (fromSum e₁ e₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.injective_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c 
: ComplexShape ι} {c' : ComplexShape ι'} (self : c.Embedding c'),   Function.Inj
ective self.f
· 使用定理 `ComplexShape.Embedding.AreComplementary.disjoint`：∀ {ι : Type u_1} {ι₁ :
 Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Com
plexShape ι₂}   {e₁ : c₁.Embedding c} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ComplexShape.Embedding.AreComplementary.union`：∀ {ι : Type u_1} {ι₁ : Ty
pe u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Comple
xShape ι₂}   {e₁ : c₁.Embedding c} …
-/
lemma fromSum_bijective : Function.Bijective (fromSum e₁ e₂) := by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ h.symm).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.inl i₁, rfl⟩
    · exact ⟨Sum.inr i₂, rfl⟩

/-- Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious bijection `ι₁ ⊕ ι₂ ≃ ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`. -/
/-
**ComplexShape.Embedding.AreComplementary.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Compl
exShape.Embedding.AreComplementary`。
形式化陈述：equiv : ι₁ oplus ι₂ ≃ ι
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.AreComplementary.fromSum_bijective`：fromSum_bijec
tive : Function.Bijective (fromSum e₁ e₂)

--- 原说明 ---
Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious bijection `ι₁ ⊕ ι₂ ≃ ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`.
-/
noncomputable def equiv : ι₁ ⊕ ι₂ ≃ ι := Equiv.ofBijective _ (ac.fromSum_bijective)
/-
**ComplexShape.Embedding.AreComplementary.equiv_inl** 是 Mathlib 中的一个定理，位于命名空间 `C
omplexShape.Embedding.AreComplementary`。
形式化陈述：∀ {ι : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ 
: ComplexShape ι₁} {c₂ : ComplexShape ι₂}   {e₁ : c₁.Embedding c} {e₂ : c₂.Embed
ding c} (ac : e₁.AreComplementary e₂) (i₁ : ι₁), ac.equiv (Sum.inl i₁) = e₁.f i₁
参数：ac : e₁.AreComplementary e₂；i₁ : ι₁；Sum.inl i₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma equiv_inl (i₁ : ι₁) : ac.equiv (Sum.inl i₁) = e₁.f i₁ := rfl
/-
**ComplexShape.Embedding.AreComplementary.equiv_inr** 是 Mathlib 中的一个定理，位于命名空间 `C
omplexShape.Embedding.AreComplementary`。
形式化陈述：∀ {ι : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ 
: ComplexShape ι₁} {c₂ : ComplexShape ι₂}   {e₁ : c₁.Embedding c} {e₂ : c₂.Embed
ding c} (ac : e₁.AreComplementary e₂) (i₂ : ι₂), ac.equiv (Sum.inr i₂) = e₂.f i₂
参数：ac : e₁.AreComplementary e₂；i₂ : ι₂；Sum.inr i₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma equiv_inr (i₂ : ι₂) : ac.equiv (Sum.inr i₂) = e₂.f i₂ := rfl

section

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

variable (X) in
/-- Auxiliary definition for `desc`. -/
/-
**ComplexShape.Embedding.AreComplementary.desc.aux** 是 Mathlib 中的一个定义，位于命名空间 `Co
mplexShape.Embedding.AreComplementary.desc`。
形式化陈述：{ι : Type u_1} → (X : ι → Type u_5) → (i j : ι) → i = j → X i ≃ X j
参数：X : ι → Type u_5；i j : ι。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Auxiliary definition for `desc`.
-/
def desc.aux (i j : ι) (hij : i = j) : X i ≃ X j := by
  subst hij
  rfl

omit ac in
@[simp]
/-
**ComplexShape.Embedding.AreComplementary.desc.aux_trans** 是 Mathlib 中的一个定理，位于命名
空间 `ComplexShape.Embedding.AreComplementary.desc`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_5} {i j k : ι} (hij : i = j) (hjk : j = k
) (x : X i),   (ComplexShape.Embedding.AreComplementary.desc.aux X j k hjk)     
  ((ComplexShape.Embedding.AreComplementary.desc.aux X i j hij) x) =     (Comple
xShape.Embedding.AreComplementary.desc.aux X i k ⋯) x
参数：hij : i = j；hjk : j = k；x : X i；ComplexShape.Embedding.AreComplementary.desc.
aux X j k hjk；(ComplexShape.Embedding.AreComplementary.desc.aux X i j hij) x；Com
plexShape.Embedding.AreComplementary.desc.aux X i k ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma desc.aux_trans {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i) :
    desc.aux X j k hjk (aux X i j hij x) = desc.aux X i k (hij.trans hjk) x := by
  subst hij hjk
  rfl

/-- Auxiliary definition for `desc`. -/
/-
**ComplexShape.Embedding.AreComplementary.desc'** 是 Mathlib 中的一个引理，位于命名空间 `Compl
exShape.Embedding.AreComplementary`。
形式化陈述：desc'_inl (i : ι₁ oplus ι₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) : ac.desc' x₁ x
₂ i = desc.aux _ _ _ (by subst h; simp) (x₁ i₁)
参数：i : ι₁ oplus ι₂；i₁ : ι₁；h : Sum.inl i₁ = i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `desc`.
-/
def desc' : ∀ (i : ι₁ ⊕ ι₂), X (ac.equiv i)
  | Sum.inl i₁ => x₁ i₁
  | Sum.inr i₂ => x₂ i₂
/-
**ComplexShape.Embedding.AreComplementary.desc'_inl** 是 Mathlib 中的一个定理，位于命名空间 `C
omplexShape.Embedding.AreComplementary`。
形式化陈述：∀ {ι : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ 
: ComplexShape ι₁} {c₂ : ComplexShape ι₂}   {e₁ : c₁.Embedding c} {e₂ : c₂.Embed
ding c} (ac : e₁.AreComplementary e₂) {X : ι → Type u_5}   (x₁ : (i₁ : ι₁) → X (
e₁.f i₁)) (x₂ : (i₂ : ι₂) → X (e₂.f i₂)) (i : ι₁ ⊕ ι₂) (i₁ : ι₁) (h : Sum.inl i₁
 = i),   ac.desc' x₁ x₂ i = (ComplexShape.Embedding.AreComplementary.desc.aux X 
(e₁.f i₁) (ac.equiv i) ⋯) (x₁ i₁)
参数：ac : e₁.AreComplementary e₂；x₁ : (i₁ : ι₁) → X (e₁.f i₁)；x₂ : (i₂ : ι₂) → X (
e₂.f i₂)；i : ι₁ ⊕ ι₂；i₁ : ι₁；h : Sum.inl i₁ = i；ComplexShape.Embedding.AreComple
mentary.desc.aux X (e₁.f i₁) (ac.equiv i) ⋯；x₁ i₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.AreComplementary.desc'`：desc'_inl (i : ι₁ oplus ι
₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) : ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst 
h; simp) (x₁ i₁)
-/
lemma desc'_inl (i : ι₁ ⊕ ι₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) :
    ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst h; simp) (x₁ i₁) := by subst h; rfl
/-
**ComplexShape.Embedding.AreComplementary.desc'_inr** 是 Mathlib 中的一个定理，位于命名空间 `C
omplexShape.Embedding.AreComplementary`。
形式化陈述：∀ {ι : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ 
: ComplexShape ι₁} {c₂ : ComplexShape ι₂}   {e₁ : c₁.Embedding c} {e₂ : c₂.Embed
ding c} (ac : e₁.AreComplementary e₂) {X : ι → Type u_5}   (x₁ : (i₁ : ι₁) → X (
e₁.f i₁)) (x₂ : (i₂ : ι₂) → X (e₂.f i₂)) (i : ι₁ ⊕ ι₂) (i₂ : ι₂) (h : Sum.inr i₂
 = i),   ac.desc' x₁ x₂ i = (ComplexShape.Embedding.AreComplementary.desc.aux X 
(e₂.f i₂) (ac.equiv i) ⋯) (x₂ i₂)
参数：ac : e₁.AreComplementary e₂；x₁ : (i₁ : ι₁) → X (e₁.f i₁)；x₂ : (i₂ : ι₂) → X (
e₂.f i₂)；i : ι₁ ⊕ ι₂；i₂ : ι₂；h : Sum.inr i₂ = i；ComplexShape.Embedding.AreComple
mentary.desc.aux X (e₂.f i₂) (ac.equiv i) ⋯；x₂ i₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.AreComplementary.desc'`：desc'_inl (i : ι₁ oplus ι
₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) : ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst 
h; simp) (x₁ i₁)
-/
lemma desc'_inr (i : ι₁ ⊕ ι₂) (i₂ : ι₂) (h : Sum.inr i₂ = i) :
    ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst h; simp) (x₂ i₂) := by subst h; rfl

/-- If `ι₁` and `ι₂` are the index types of complementary embeddings into a
complex shape of index type `ι`, this is a constructor for (dependent) maps from `ι`,
which takes as inputs the "restrictions" to `ι₁` and `ι₂`. -/
/-
**ComplexShape.Embedding.AreComplementary.desc** 是 Mathlib 中的一个定义，位于命名空间 `Comple
xShape.Embedding.AreComplementary`。
形式化陈述：desc (i : ι) : X i
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `ComplexShape.Embedding.AreComplementary.desc'`：desc'_inl (i : ι₁ oplus ι
₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) : ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst 
h; simp) (x₁ i₁)

--- 原说明 ---
If `ι₁` and `ι₂` are the index types of complementary embeddings into a
complex shape of index type `ι`, this is a constructor for (dependent) maps from
 `ι`,
which takes as inputs the "restrictions" to `ι₁` and `ι₂`.
-/
noncomputable def desc (i : ι) : X i :=
  desc.aux _ _ _ (by simp) (ac.desc' x₁ x₂ (ac.equiv.symm i))
/-
**ComplexShape.Embedding.AreComplementary.desc_inl** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplexShape.Embedding.AreComplementary`。
形式化陈述：desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁
参数：i₁ : ι₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `ComplexShape.Embedding.AreComplementary.desc'`：desc'_inl (i : ι₁ oplus ι
₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) : ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst 
h; simp) (x₁ i₁)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.Embedding.AreComplementary.desc'_inl`：∀ {ι : Type u_1} {ι₁ 
: Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Co
mplexShape ι₂}   {e₁ : c₁.Embedding c} …
· 使用定理 `ComplexShape.Embedding.AreComplementary.desc.aux_trans`：∀ {ι : Type u_1}
 {X : ι → Type u_5} {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i),   (Comple
xShape.Embedding.AreComplementary.desc.aux X…
-/
lemma desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁ := by
  dsimp [desc]
  rw [ac.desc'_inl _ _ _ i₁ (ac.equiv.injective (by simp)), desc.aux_trans]
  rfl
/-
**ComplexShape.Embedding.AreComplementary.desc_inr** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplexShape.Embedding.AreComplementary`。
形式化陈述：desc_inr (i₂ : ι₂) : ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂
参数：i₂ : ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `ComplexShape.Embedding.AreComplementary.desc'`：desc'_inl (i : ι₁ oplus ι
₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) : ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst 
h; simp) (x₁ i₁)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.Embedding.AreComplementary.desc'_inr`：∀ {ι : Type u_1} {ι₁ 
: Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Co
mplexShape ι₂}   {e₁ : c₁.Embedding c} …
· 使用定理 `ComplexShape.Embedding.AreComplementary.desc.aux_trans`：∀ {ι : Type u_1}
 {X : ι → Type u_5} {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i),   (Comple
xShape.Embedding.AreComplementary.desc.aux X…
-/
lemma desc_inr (i₂ : ι₂) : ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂ := by
  dsimp [desc]
  rw [ac.desc'_inr _ _ _ i₂ (ac.equiv.injective (by simp)), desc.aux_trans]
  rfl

end

variable (K L : HomologicalComplex C c)

/-
**ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside** 是 Mathlib
 中的一个引理，位于命名空间 `ComplexShape.Embedding.AreComplementary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isStrictlySupportedOutside₁_iff :
    K.IsStrictlySupportedOutside e₁ ↔ K.IsStrictlySupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.isZero i₁⟩
  · intro _
    exact ⟨fun i₁ => K.isZero_X_of_isStrictlySupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩
/-
**ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside** 是 Mathlib
 中的一个引理，位于命名空间 `ComplexShape.Embedding.AreComplementary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isStrictlySupportedOutside₂_iff :
    K.IsStrictlySupportedOutside e₂ ↔ K.IsStrictlySupported e₁ :=
  ac.symm.isStrictlySupportedOutside₁_iff K
/-
**ComplexShape.Embedding.AreComplementary.isSupportedOutside** 是 Mathlib 中的一个引理，
位于命名空间 `ComplexShape.Embedding.AreComplementary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isSupportedOutside₁_iff :
    K.IsSupportedOutside e₁ ↔ K.IsSupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.exactAt i₁⟩
  · intro _
    exact ⟨fun i₁ => K.exactAt_of_isSupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩
/-
**ComplexShape.Embedding.AreComplementary.isSupportedOutside** 是 Mathlib 中的一个引理，
位于命名空间 `ComplexShape.Embedding.AreComplementary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isSupportedOutside₂_iff :
    K.IsSupportedOutside e₂ ↔ K.IsSupported e₁ :=
  ac.symm.isSupportedOutside₁_iff K

variable {K L}

/-- Variant of `hom_ext`. -/
/-
**ComplexShape.Embedding.AreComplementary.hom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `Co
mplexShape.Embedding.AreComplementary`。
形式化陈述：hom_ext' (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂) (hL : L.IsStri
ctlySupportedOutside e₁) : φ = 0
参数：φ : K ⟶ L；hK : K.IsStrictlySupportedOutside e₂；hL : L.IsStrictlySupportedOuts
ide e₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `ComplexShape.Embedding.AreComplementary.union`：∀ {ι : Type u_1} {ι₁ : Ty
pe u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Comple
xShape ι₂}   {e₁ : c₁.Embedding c} …
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `HomologicalComplex.IsStrictlySupportedOutside.isZero`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g

--- 原说明 ---
Variant of `hom_ext`.
-/
lemma hom_ext' (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂)
    (hL : L.IsStrictlySupportedOutside e₁) :
    φ = 0 := by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src
/-
**ComplexShape.Embedding.AreComplementary.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Com
plexShape.Embedding.AreComplementary`。
形式化陈述：hom_ext [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L) 
: φ = 0
参数：φ : K ⟶ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.AreComplementary.hom_ext'`：hom_ext' (φ : K ⟶ L) (
hK : K.IsStrictlySupportedOutside e₂) (hL : L.IsStrictlySupportedOutside e₁) : φ
 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₂_iff`
：isStrictlySupportedOutside₂_iff : K.IsStrictlySupportedOutside e₂ ↔ K.IsStrictl
ySupported e₁
· 使用引理 `ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₁_iff`
：isStrictlySupportedOutside₁_iff : K.IsStrictlySupportedOutside e₁ ↔ K.IsStrictl
ySupported e₂
-/
lemma hom_ext [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L) :
    φ = 0 := by
  apply ac.hom_ext'
  · rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  · rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

/-- If `e₁` and `e₂` are complementary embeddings into a complex shape `c`,
indices `i₁` and `i₂` are at the boundary if `c.Rel (e₁.f i₁) (e₂.f i₂)`. -/
@[nolint unusedArguments]
/-
**ComplexShape.Embedding.AreComplementary.Boundary** 是 Mathlib 中的一个定义，位于命名空间 `Co
mplexShape.Embedding.AreComplementary`。
形式化陈述：Boundary (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂) : Prop
参数：_ : AreComplementary e₁ e₂；i₁ : ι₁；i₂ : ι₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e₁` and `e₂` are complementary embeddings into a complex shape `c`,
indices `i₁` and `i₂` are at the boundary if `c.Rel (e₁.f i₁) (e₂.f i₂)`.
-/
def Boundary (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂) : Prop :=
  c.Rel (e₁.f i₁) (e₂.f i₂)

namespace Boundary

variable {ac}

section

variable {i₁ : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂)

include h

/-
**ComplexShape.Embedding.AreComplementary.Boundary.fst** 是 Mathlib 中的一个引理，位于命名空间
 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：fst : e₁.BoundaryLE i₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.boundaryLE`：boundaryLE {k' : ι'} {j : ι} (hj : c'
.Rel (e.f j) k') (hk' : forall i, e.f i != k') : e.BoundaryLE j
· 使用定理 `ComplexShape.Embedding.AreComplementary.disjoint`：∀ {ι : Type u_1} {ι₁ :
 Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Com
plexShape ι₂}   {e₁ : c₁.Embedding c} …
-/
lemma fst : e₁.BoundaryLE i₁ :=
  e₁.boundaryLE h (fun _ => ac.disjoint _ _)
/-
**ComplexShape.Embedding.AreComplementary.Boundary.snd** 是 Mathlib 中的一个引理，位于命名空间
 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：snd : e₂.BoundaryGE i₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.boundaryGE`：boundaryGE {i' : ι'} {j : ι} (hj : c'
.Rel i' (e.f j)) (hi' : forall i, e.f i != i') : e.BoundaryGE j
· 使用定理 `ComplexShape.Embedding.AreComplementary.disjoint`：∀ {ι : Type u_1} {ι₁ :
 Type u_2} {ι₂ : Type u_3} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : Com
plexShape ι₂}   {e₁ : c₁.Embedding c} …
· 使用引理 `ComplexShape.Embedding.AreComplementary.symm`：symm : AreComplementary e₂
 e₁ where disjoint i₂ i₁
-/
lemma snd : e₂.BoundaryGE i₂ :=
  e₂.boundaryGE h (fun _ => ac.symm.disjoint _ _)

end

/-
**ComplexShape.Embedding.AreComplementary.Boundary.fst_inj** 是 Mathlib 中的一个引理，位于
命名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：fst_inj {i₁ i₁' : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary 
i₁' i₂) : i₁ = i₁'
参数：h : ac.Boundary i₁ i₂；h' : ac.Boundary i₁' i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.injective_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c 
: ComplexShape ι} {c' : ComplexShape ι'} (self : c.Embedding c'),   Function.Inj
ective self.f
· 使用定理 `ComplexShape.prev_eq`：∀ {ι : Type u_1} (self : ComplexShape ι) {i i' j :
 ι}, self.Rel i j → self.Rel i' j → i = i'
-/
lemma fst_inj {i₁ i₁' : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁' i₂) :
    i₁ = i₁' :=
  e₁.injective_f (c.prev_eq h h')
/-
**ComplexShape.Embedding.AreComplementary.Boundary.snd_inj** 是 Mathlib 中的一个引理，位于
命名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：snd_inj {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary 
i₁ i₂') : i₂ = i₂'
参数：h : ac.Boundary i₁ i₂；h' : ac.Boundary i₁ i₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.injective_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c 
: ComplexShape ι} {c' : ComplexShape ι'} (self : c.Embedding c'),   Function.Inj
ective self.f
· 使用定理 `ComplexShape.next_eq`：∀ {ι : Type u_1} (self : ComplexShape ι) {i j j' :
 ι}, self.Rel i j → self.Rel i j' → j = j'
-/
lemma snd_inj {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁ i₂') :
    i₂ = i₂' :=
  e₂.injective_f (c.next_eq h h')

variable (ac)
/-
**ComplexShape.Embedding.AreComplementary.Boundary.exists** 是 Mathlib 中的一个引理，位于命
名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists₁ {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ∃ i₂, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₂, hi₂⟩ := ac.exists_i₂ (c.next (e₁.f i₁))
    (fun i₁' hi₁' => h₂ i₁' (by simpa only [← hi₁'] using! h₁))
  exact ⟨i₂, by simpa only [hi₂] using! h₁⟩
/-
**ComplexShape.Embedding.AreComplementary.Boundary.exists** 是 Mathlib 中的一个引理，位于命
名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists₂ {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ∃ i₁, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₁, hi₁⟩ := ac.exists_i₁ (c.prev (e₂.f i₂))
    (fun i₂' hi₂' => h₂ i₂' (by simpa only [← hi₂'] using! h₁))
  exact ⟨i₁, by simpa only [hi₁] using! h₁⟩

/-- If `ac : AreComplementary e₁ e₂` (with `e₁ : ComplexShape.Embedding c₁ c` and
`e₂ : ComplexShape.Embedding c₂ c`), and `i₁` belongs to `e₁.BoundaryLE`,
then this is the (unique) index `i₂` of `c₂` such that `ac.Boundary i₁ i₂`. -/
/-
**ComplexShape.Embedding.AreComplementary.Boundary.indexOfBoundaryLE** 是 Mathlib
 中的一个定义，位于命名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：indexOfBoundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) : ι₂
参数：h : e₁.BoundaryLE i₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.AreComplementary.Boundary.exists₁`：exists₁ {i₁ : 
ι₁} (h : e₁.BoundaryLE i₁) : exists i₂, ac.Boundary i₁ i₂

--- 原说明 ---
If `ac : AreComplementary e₁ e₂` (with `e₁ : ComplexShape.Embedding c₁ c` and
`e₂ : ComplexShape.Embedding c₂ c`), and `i₁` belongs to `e₁.BoundaryLE`,
then this is the (unique) index `i₂` of `c₂` such that `ac.Boundary i₁ i₂`.
-/
noncomputable def indexOfBoundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) : ι₂ :=
    (exists₁ ac h).choose
/-
**ComplexShape.Embedding.AreComplementary.Boundary.of_boundaryLE** 是 Mathlib 中的一
个引理，位于命名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) : ac.Boundary i₁ (indexOfBo
undaryLE ac h)
参数：h : e₁.BoundaryLE i₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `ComplexShape.Embedding.AreComplementary.Boundary.exists₁`：exists₁ {i₁ : 
ι₁} (h : e₁.BoundaryLE i₁) : exists i₂, ac.Boundary i₁ i₂
-/
lemma of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ac.Boundary i₁ (indexOfBoundaryLE ac h) := (exists₁ ac h).choose_spec

/-- If `ac : AreComplementary e₁ e₂` (with `e₁ : ComplexShape.Embedding c₁ c` and
`e₂ : ComplexShape.Embedding c₂ c`), and `i₂` belongs to `e₂.BoundaryGE`,
then this is the (unique) index `i₁` of `c₁` such that `ac.Boundary i₁ i₂`. -/
/-
**ComplexShape.Embedding.AreComplementary.Boundary.indexOfBoundaryGE** 是 Mathlib
 中的一个定义，位于命名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：indexOfBoundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) : ι₁
参数：h : e₂.BoundaryGE i₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.AreComplementary.Boundary.exists₂`：exists₂ {i₂ : 
ι₂} (h : e₂.BoundaryGE i₂) : exists i₁, ac.Boundary i₁ i₂

--- 原说明 ---
If `ac : AreComplementary e₁ e₂` (with `e₁ : ComplexShape.Embedding c₁ c` and
`e₂ : ComplexShape.Embedding c₂ c`), and `i₂` belongs to `e₂.BoundaryGE`,
then this is the (unique) index `i₁` of `c₁` such that `ac.Boundary i₁ i₂`.
-/
noncomputable def indexOfBoundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) : ι₁ :=
    (exists₂ ac h).choose
/-
**ComplexShape.Embedding.AreComplementary.Boundary.of_boundaryGE** 是 Mathlib 中的一
个引理，位于命名空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) : ac.Boundary (indexOfBound
aryGE ac h) i₂
参数：h : e₂.BoundaryGE i₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `ComplexShape.Embedding.AreComplementary.Boundary.exists₂`：exists₂ {i₂ : 
ι₂} (h : e₂.BoundaryGE i₂) : exists i₁, ac.Boundary i₁ i₂
-/
lemma of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ac.Boundary (indexOfBoundaryGE ac h) i₂ := (exists₂ ac h).choose_spec

/-- The bijection `Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE` when
`e₁` and `e₂` are complementary embeddings of complex shapes. -/
/-
**ComplexShape.Embedding.AreComplementary.Boundary.equiv** 是 Mathlib 中的一个定义，位于命名
空间 `ComplexShape.Embedding.AreComplementary.Boundary`。
形式化陈述：equiv : Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE` when
`e₁` and `e₂` are complementary embeddings of complex shapes.
-/
noncomputable def equiv : Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE where
  toFun := fun ⟨i₁, h⟩ => ⟨_, (of_boundaryLE ac h).snd⟩
  invFun := fun ⟨i₂, h⟩ => ⟨_, (of_boundaryGE ac h).fst⟩
  left_inv := fun ⟨i₁, h⟩ => by
    ext
    have h' := of_boundaryLE ac h
    have h'' := of_boundaryGE ac h'.snd
    exact fst_inj h'' h'
  right_inv := fun ⟨i₂, h⟩ => by
    ext
    have h' := of_boundaryGE ac h
    have h'' := of_boundaryLE ac h'.fst
    exact snd_inj h'' h'

end Boundary

end AreComplementary

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.Embedding.embeddingUpInt_areComplementary** 是 Mathlib 中的一个引理，位于命名
空间 `ComplexShape.Embedding`。
形式化陈述：embeddingUpInt_areComplementary (n₀ n₁ : Int) (h : n₀ + 1 = n₁) : AreCompl
ementary (embeddingUpIntLE n₀) (embeddingUpIntGE n₁) where disjoint i₁ i₂
参数：n₀ n₁ : Int；h : n₀ + 1 = n₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Int.exists_add_of_le`：∀ {a b : ℤ}, a ≤ b → ∃ c, b = a + ↑c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma embeddingUpInt_areComplementary (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    AreComplementary (embeddingUpIntLE n₀) (embeddingUpIntGE n₁) where
  disjoint i₁ i₂ := by dsimp; lia
  union i := by
    by_cases hi : i ≤ n₀
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; lia⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ ≤ i by lia)
      exact Or.inr ⟨k, rfl⟩

end Embedding

end ComplexShape

namespace HomologicalComplex

section

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

/-- When `e₁` and `e₂` are complementary embeddings of complex shapes, with
`e₁.IsTruncLE` and `e₂.IsTruncGE`, then this is the canonical quasi-isomorphism
`(K.shortComplexTruncLE e₁).X₃ ⟶ K.truncGE e₂` where
`(K.shortComplexTruncLE e₁).X₃` is the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁ ⟶ K`. -/
/-
**HomologicalComplex.shortComplexTruncLEX** 是 Mathlib 中的一个定义，位于命名空间 `Homological
Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `e₁` and `e₂` are complementary embeddings of complex shapes, with
`e₁.IsTruncLE` and `e₂.IsTruncGE`, then this is the canonical quasi-isomorphism
`(K.shortComplexTruncLE e₁).X₃ ⟶ K.truncGE e₂` where
`(K.shortComplexTruncLE e₁).X₃` is the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁
 ⟶ K`.
-/
noncomputable def shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).X₃ ⟶ K.truncGE e₂ :=
  cokernel.desc _ (K.πTruncGE e₂) (ac.hom_ext _)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.g_shortComplexTruncLEX** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).g ≫ K.shortComplexTruncLEX₃ToTruncGE ac = K.πTruncGE e₂ :=
  cokernel.π_desc _ _ _

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso (K.shortComplexTruncLEX₃ToTruncGE ac) where
  quasiIsoAt i := by
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
    · have h₁ := ((ac.isSupportedOutside₁_iff (K.truncGE e₂)).2 inferInstance).exactAt i₁
      have h₂ := (K.shortComplexTruncLE_X₃_isSupportedOutside e₁).exactAt i₁
      simpa only [quasiIsoAt_iff_exactAt _ _ h₂] using h₁
    · have := quasiIsoAt_shortComplexTruncLE_g K e₁ (e₂.f i₂) (fun _ => ac.disjoint _ _)
      rw [← quasiIsoAt_iff_comp_left (K.shortComplexTruncLE e₁).g
        (K.shortComplexTruncLEX₃ToTruncGE ac), g_shortComplexTruncLEX₃ToTruncGE]
      dsimp
      infer_instance

end

end HomologicalComplex

