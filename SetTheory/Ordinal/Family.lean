/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Arithmetic on families of ordinals

This file proves basic results about the suprema of families of ordinals.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

@[expose] public noncomputable section

assert_not_exists Field Module

open Function Cardinal Set Order

universe u v w

namespace Ordinal

variable {α β : Type*}

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a specified
well-ordering. -/
@[deprecated enum (since := "2026-04-06")]
/-
**Ordinal.bfamilyOfFamily'** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：bfamilyOfFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : 
ι -> α) : forall a < type r, α
参数：r : ι -> ι -> Prop；f : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using
 a specified
well-ordering.
-/
def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    ∀ a < type r, α := fun a ha => f (enum r ⟨a, ha⟩)

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
@[deprecated enum (since := "2026-04-06")]
/-
**Ordinal.bfamilyOfFamily** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：bfamilyOfFamily {ι : Type u} : (ι -> α) -> forall a < type (@WellOrderingR
el ι), α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using
 a well-ordering
given by the axiom of choice.
-/
def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀ a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a specified
well-ordering. -/
@[deprecated typein (since := "2026-04-06")]
/-
**Ordinal.familyOfBFamily'** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：familyOfBFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o} (
ho : type r = o) (f : forall a < o, α) : ι -> α
参数：r : ι -> ι -> Prop；ho : type r = o；f : forall a < o, α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using
 a specified
well-ordering.
-/
def familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, α) : ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
@[deprecated typein (since := "2026-04-06")]
/-
**Ordinal.familyOfBFamily** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：familyOfBFamily (o : Ordinal) (f : forall a < o, α) : o.ToType -> α
参数：o : Ordinal；f : forall a < o, α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o

--- 原说明 ---
Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using
 a well-ordering
given by the axiom of choice.
-/
def familyOfBFamily (o : Ordinal) (f : ∀ a < o, α) : o.ToType → α :=
  familyOfBFamily' (· < ·) (type_toType o) f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.bfamilyOfFamily'_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} (r : ι → ι → Prop) [inst : IsWellOrder ι r
] (f : ι → α) (i : ι),   Ordinal.bfamilyOfFamily' r f ((Ordinal.typein r).toRelE
mbedding i) ⋯ = f i
参数：r : ι → ι → Prop；f : ι → α；i : ι；(Ordinal.typein r).toRelEmbedding i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bfamilyOfFamily'_typein {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) (i) :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by
  simp only [bfamilyOfFamily', enum_typein]

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.bfamilyOfFamily_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bfamilyOfFamily_typein {ι} (f : ι -> α) (i) : bfamilyOfFamily f (typein _ 
i) (typein_lt_type _ i) = f i
参数：f : ι -> α；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bfamilyOfFamily'_typein`：∀ {α : Type u_1} {ι : Type u_3} (r : ι 
→ ι → Prop) [inst : IsWellOrder ι r] (f : ι → α) (i : ι),   Ordinal.bfamilyOfFam
ily' r f ((Ordinal.ty…
-/
theorem bfamilyOfFamily_typein {ι} (f : ι → α) (i) :
    bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i :=
  bfamilyOfFamily'_typein _ f i

set_option backward.isDefEq.respectTransparency false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.familyOfBFamily'_enum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {α : Type u_1} {ι : Type u} (r : ι → ι → Prop) [inst : IsWellOrder ι r] 
{o : Ordinal.{u}} (ho : Ordinal.type r = o)   (f : (a : Ordinal.{u}) → a < o → α
) (i : Ordinal.{u}) (hi : i < o),   Ordinal.familyOfBFamily' r ho f ((Ordinal.en
um r) ⟨i, ⋯⟩) = f i hi
参数：r : ι → ι → Prop；ho : Ordinal.type r = o；f : (a : Ordinal.{u}) → a < o → α；i 
: Ordinal.{u}；hi : i < o；(Ordinal.enum r) ⟨i, ⋯⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem familyOfBFamily'_enum {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily' r ho f (enum r ⟨i, by rwa [ho]⟩) = f i hi := by
  simp only [familyOfBFamily', typein_enum]

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.familyOfBFamily_enum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：familyOfBFamily_enum (o : Ordinal) (f : forall a < o, α) (i hi) : familyOf
BFamily o f (enum (α
参数：o : Ordinal；f : forall a < o, α；i hi。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.familyOfBFamily'_enum`：∀ {α : Type u_1} {ι : Type u} (r : ι → ι 
→ Prop) [inst : IsWellOrder ι r] {o : Ordinal.{u}} (ho : Ordinal.type r = o)   (
f : (a : Ordinal.{u…
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem familyOfBFamily_enum (o : Ordinal) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily o f (enum (α := o.ToType) (· < ·) ⟨i, hi.trans_eq (type_toType _).symm⟩)
    = f i hi :=
  familyOfBFamily'_enum _ (type_toType o) f _ _

/-- The range of a family indexed by ordinals. -/
@[deprecated range (since := "2026-04-06")]
/-
**Ordinal.brange** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：brange (o : Ordinal) (f : forall a < o, α) : Set α
参数：o : Ordinal；f : forall a < o, α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a family indexed by ordinals.
-/
def brange (o : Ordinal) (f : ∀ a < o, α) : Set α :=
  { a | ∃ i hi, f i hi = a }

@[deprecated mem_range (since := "2026-04-06")]
/-
**Ordinal.mem_brange** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_brange {o : Ordinal} {f : forall a < o, α} {a} : a in brange o f ↔ exi
sts i hi, f i hi = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_brange {o : Ordinal} {f : ∀ a < o, α} {a} : a ∈ brange o f ↔ ∃ i hi, f i hi = a :=
  Iff.rfl

@[deprecated mem_range_self (since := "2026-04-06")]
/-
**Ordinal.mem_brange_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_brange_self {o} (f : forall a < o, α) (i hi) : f i hi in brange o f
参数：f : forall a < o, α；i hi。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_brange_self {o} (f : ∀ a < o, α) (i hi) : f i hi ∈ brange o f :=
  ⟨i, hi, rfl⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.range_familyOfBFamily'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：range_familyOfBFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r]
 {o} (ho : type r = o) (f : forall a < o, α) : range (familyOfBFamily' r ho f) =
 brange o f
参数：r : ι -> ι -> Prop；ho : type r = o；f : forall a < o, α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ordinal.mem_brange_self`：mem_brange_self {o} (f : forall a < o, α) (i hi
) : f i hi in brange o f
· 使用定理 `Ordinal.familyOfBFamily'_enum`：∀ {α : Type u_1} {ι : Type u} (r : ι → ι 
→ Prop) [inst : IsWellOrder ι r] {o : Ordinal.{u}} (ho : Ordinal.type r = o)   (
f : (a : Ordinal.{u…
-/
theorem range_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) : range (familyOfBFamily' r ho f) = brange o f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.range_familyOfBFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：range_familyOfBFamily {o} (f : forall a < o, α) : range (familyOfBFamily o
 f) = brange o f
参数：f : forall a < o, α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.range_familyOfBFamily'`：range_familyOfBFamily' {ι : Type u} (r :
 ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho : type r = o) (f : forall a < o, α) :
 range (familyOfBFam…
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem range_familyOfBFamily {o} (f : ∀ a < o, α) : range (familyOfBFamily o f) = brange o f :=
  range_familyOfBFamily' _ _ f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.brange_bfamilyOfFamily'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：brange_bfamilyOfFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r
] (f : ι -> α) : brange _ (bfamilyOfFamily' r f) = range f
参数：r : ι -> ι -> Prop；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `Ordinal.bfamilyOfFamily'_typein`：∀ {α : Type u_1} {ι : Type u_3} (r : ι 
→ ι → Prop) [inst : IsWellOrder ι r] (f : ι → α) (i : ι),   Ordinal.bfamilyOfFam
ily' r f ((Ordinal.ty…
-/
theorem brange_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    brange _ (bfamilyOfFamily' r f) = range f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.brange_bfamilyOfFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：brange_bfamilyOfFamily {ι : Type u} (f : ι -> α) : brange _ (bfamilyOfFami
ly f) = range f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.brange_bfamilyOfFamily'`：brange_bfamilyOfFamily' {ι : Type u} (r
 : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α) : brange _ (bfamilyOfFamily' r
 f) = range f
-/
theorem brange_bfamilyOfFamily {ι : Type u} (f : ι → α) : brange _ (bfamilyOfFamily f) = range f :=
  brange_bfamilyOfFamily' _ _

@[deprecated "brange is deprecated" (since := "2026-04-06")]
/-
**Ordinal.brange_const** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：brange_const {o : Ordinal} (ho : o != 0) {c : α} : (brange o fun _ _ => c)
 = {c}
参数：ho : o != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.range_familyOfBFamily`：range_familyOfBFamily {o} (f : forall a <
 o, α) : range (familyOfBFamily o f) = brange o f
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.nonempty_toType_iff`：nonempty_toType_iff {o : Ordinal} : Nonempt
y o.ToType ↔ o != 0
-/
theorem brange_const {o : Ordinal} (ho : o ≠ 0) {c : α} : (brange o fun _ _ => c) = {c} := by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.ToType (nonempty_toType_iff.2 ho) c

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.comp_bfamilyOfFamily'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：comp_bfamilyOfFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] 
(f : ι -> α) (g : α -> β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamil
yOfFamily' r (g ∘ f)
参数：r : ι -> ι -> Prop；f : ι -> α；g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α)
    (g : α → β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) :=
  rfl

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.comp_bfamilyOfFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：comp_bfamilyOfFamily {ι : Type u} (f : ι -> α) (g : α -> β) : (fun i hi =>
 g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f)
参数：f : ι -> α；g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_bfamilyOfFamily {ι : Type u} (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) :=
  rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.comp_familyOfBFamily'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：comp_familyOfBFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] 
{o} (ho : type r = o) (f : forall a < o, α) (g : α -> β) : g ∘ familyOfBFamily' 
r ho f = familyOfBFamily' r ho fun i hi => g (f i hi)
参数：r : ι -> ι -> Prop；ho : type r = o；f : forall a < o, α；g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily' r ho f = familyOfBFamily' r ho fun i hi => g (f i hi) :=
  rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.comp_familyOfBFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：comp_familyOfBFamily {o} (f : forall a < o, α) (g : α -> β) : g ∘ familyOf
BFamily o f = familyOfBFamily o fun i hi => g (f i hi)
参数：f : forall a < o, α；g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_familyOfBFamily {o} (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily o f = familyOfBFamily o fun i hi => g (f i hi) :=
  rfl

/-! ### Supremum of a family of ordinals -/

/-
**Ordinal.bddAbove_of_small** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_of_small {s : Set Ordinal.{u}} [Small.{u} s] : BddAbove s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
### Supremum of a family of ordinals
-/
theorem bddAbove_of_small {s : Set Ordinal.{u}} [Small.{u} s] : BddAbove s := by
  obtain ⟨a, ha⟩ := Cardinal.bddAbove_of_small (s := (succ ∘ card) '' s)
  refine ⟨a.ord, fun b hb ↦ le_of_lt ?_⟩
  simpa [lt_ord] using ha (mem_image_of_mem _ hb)

@[deprecated bddAbove_of_small (since := "2026-04-04")]
/-
**Ordinal.bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_range {ι : Type u} (f : ι -> Ordinal.{max u v}) : BddAbove (Set.r
ange f)
参数：f : ι -> Ordinal.{max u v}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem bddAbove_range {ι : Type u} (f : ι → Ordinal.{max u v}) : BddAbove (Set.range f) :=
  bddAbove_of_small
/-
**Ordinal.bddAbove_iff_small** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
-/
theorem bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, h⟩ ↦ small_subset (s := Iic a) fun _ hx ↦ h hx, fun _ ↦ bddAbove_of_small⟩
/-
**Ordinal.bddAbove_image** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_image {s : Set Ordinal.{u}} (hf : BddAbove s) (f : Ordinal.{u} ->
 Ordinal.{max u v}) : BddAbove (f '' s)
参数：hf : BddAbove s；f : Ordinal.{u} -> Ordinal.{max u v}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.bddAbove_iff_small`：bddAbove_iff_small {s : Set Ordinal.{u}} : B
ddAbove s ↔ Small.{u} s
· 使用定理 `small_lift`：small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w}
 α
-/
theorem bddAbove_image {s : Set Ordinal.{u}} (hf : BddAbove s)
    (f : Ordinal.{u} → Ordinal.{max u v}) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hf ⊢
  exact small_lift _
/-
**Ordinal.bddAbove_range_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_range_comp {ι : Type u} {f : ι -> Ordinal.{v}} (hf : BddAbove (ra
nge f)) (g : Ordinal.{v} -> Ordinal.{max v w}) : BddAbove (range (g ∘ f))
参数：hf : BddAbove (range f)；g : Ordinal.{v} -> Ordinal.{max v w}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Ordinal.bddAbove_image`：bddAbove_image {s : Set Ordinal.{u}} (hf : BddAb
ove s) (f : Ordinal.{u} -> Ordinal.{max u v}) : BddAbove (f '' s)
-/
theorem bddAbove_range_comp {ι : Type u} {f : ι → Ordinal.{v}} (hf : BddAbove (range f))
    (g : Ordinal.{v} → Ordinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image hf g

/-- `le_ciSup` whenever the input type is small in the output universe. This lemma sometimes
fails to infer `f` in simple cases and needs it to be given explicitly. -/
/-
**Ordinal.le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} ι] (i : ι), f i ≤ ⨆
 i, f i
参数：f : ι → Ordinal.{u}；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s

--- 原说明 ---
`le_ciSup` whenever the input type is small in the output universe. This lemma s
ometimes
fails to infer `f` in simple cases and needs it to be given explicitly.
-/
protected theorem le_iSup {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] : ∀ i, f i ≤ ⨆ i, f i :=
  le_ciSup bddAbove_of_small

/-- `ciSup_le_iff'` whenever the input type is small in the output universe. -/
@[simp]
/-
**Ordinal.iSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u, u_3} ι
], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s

--- 原说明 ---
`ciSup_le_iff'` whenever the input type is small in the output universe.
-/
protected theorem iSup_le_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  ciSup_le_iff' bddAbove_of_small

/-- An alias of `ciSup_le'` for discoverability. -/
/-
**Ordinal.iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{u_4}}, (∀ (i : ι), 
f i ≤ a) → ⨆ i, f i ≤ a
参数：∀ (i : ι), f i ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a

--- 原说明 ---
An alias of `ciSup_le'` for discoverability.
-/
protected theorem iSup_le {ι} {f : ι → Ordinal} {a} : (∀ i, f i ≤ a) → ⨆ i, f i ≤ a :=
  ciSup_le'

/-- `lt_ciSup_iff'` whenever the input type is small in the output universe. -/
@[simp]
/-
**Ordinal.lt_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u, u_3} ι
], a < ⨆ i, f i ↔ ∃ i, a < f i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_ciSup_iff'`：lt_ciSup_iff' {f : ι -> α} (h : BddAbove (range f)) : a <
 iSup f ↔ exists i, a < f i
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s

--- 原说明 ---
`lt_ciSup_iff'` whenever the input type is small in the output universe.
-/
protected theorem lt_iSup_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    a < ⨆ i, f i ↔ ∃ i, a < f i :=
  lt_ciSup_iff' bddAbove_of_small
/-
**Ordinal.lt_iSup_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_iSup_add_one {ι} (f : ι -> Ordinal.{u}) [Small.{u} ι] (i) : f i < ⨆ i, 
f i + 1
参数：f : ι -> Ordinal.{u}；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.add_one_le_iff`：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
-/
theorem lt_iSup_add_one {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] (i) : f i < ⨆ i, f i + 1 := by
  rw [← add_one_le_iff]
  apply Ordinal.le_iSup
/-
**Ordinal.iSup_add_one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_add_one_le_iff {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u
} ι] : ⨆ i, f i + 1 <= a ↔ forall i, f i < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_add_one_le_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    ⨆ i, f i + 1 ≤ a ↔ ∀ i, f i < a := by
  simp
/-
**Ordinal.iSup_add_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_add_one_le {ι} {f : ι -> Ordinal.{u}} {a} (h : forall i, f i < a) : ⨆
 i, f i + 1 <= a
参数：h : forall i, f i < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem iSup_add_one_le {ι} {f : ι → Ordinal.{u}} {a} (h : ∀ i, f i < a) : ⨆ i, f i + 1 ≤ a :=
  ciSup_le' (by simpa)
/-
**Ordinal.lt_iSup_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_iSup_add_one_iff {ι} {f : ι -> Ordinal.{u}} {a} [Small.{u} ι] : a < ⨆ i
, f i + 1 ↔ exists i, a <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iSup_add_one_iff {ι} {f : ι → Ordinal.{u}} {a} [Small.{u} ι] :
    a < ⨆ i, f i + 1 ↔ ∃ i, a ≤ f i := by
  simp

-- TODO: state in terms of `IsSuccLimit`.
/-
**Ordinal.succ_lt_iSup_of_ne_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_lt_iSup_of_ne_iSup {ι} {f : ι -> Ordinal.{u}} [Small.{u} ι] (hf : for
all i, f i != iSup f) {a} (hao : a < iSup f) : succ a < iSup f
参数：hf : forall i, f i != iSup f；hao : a < iSup f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
-/
theorem succ_lt_iSup_of_ne_iSup {ι} {f : ι → Ordinal.{u}} [Small.{u} ι]
    (hf : ∀ i, f i ≠ iSup f) {a} (hao : a < iSup f) : succ a < iSup f := by
  by_contra! hoa
  exact hao.not_ge (Ordinal.iSup_le fun i ↦ le_of_lt_succ <|
    ((Ordinal.le_iSup _ _).lt_of_ne (hf i)).trans_le hoa)

-- TODO: generalize to conditionally complete lattices.
/-
**Ordinal.iSup_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_zero_iff {ι} {f : ι -> Ordinal.{u}} [Small.{u} ι] : iSup f = 0 ↔ f
orall i, f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
-/
theorem iSup_eq_zero_iff {ι} {f : ι → Ordinal.{u}} [Small.{u} ι] :
    iSup f = 0 ↔ ∀ i, f i = 0 := by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (Ordinal.iSup_le fun i => nonpos_iff_eq_zero.2 (h i)) zero_le⟩
  rw [← nonpos_iff_eq_zero, ← h]
  exact Ordinal.le_iSup f i

@[deprecated congrArg (since := "2026-03-27")]
/-
**Ordinal.iSup_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_of_range_eq {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal} (h : Set
.range f = Set.range g) : iSup f = iSup g
参数：h : Set.range f = Set.range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem iSup_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : iSup f = iSup g :=
  congr_arg _ h

-- TODO: generalize to conditionally complete lattices
/-
**Ordinal.iSup_sum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_sum {α β} (f : α oplus β -> Ordinal.{u}) [Small.{u} α] [Small.{u} β] 
: iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b))
参数：f : α oplus β -> Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `csSup_le_csSup'`：csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s
 subseteq t) : sSup s <= sSup t
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem iSup_sum {α β} (f : α ⊕ β → Ordinal.{u}) [Small.{u} α] [Small.{u} β] :
    iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b)) := by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x ↦ f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x ↦ f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' bddAbove_of_small
    rintro i ⟨a, rfl⟩
    apply mem_range_self
/-
**Ordinal.unbounded_range_of_le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：unbounded_range_of_le_iSup {α β : Type u} (r : α -> α -> Prop) [IsWellOrde
r α r] (f : β -> α) (h : type r <= ⨆ i, typein r (f i)) : Unbounded r (range f)
参数：r : α -> α -> Prop；f : β -> α；h : type r <= ⨆ i, typein r (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.typein_lt_typein`：typein_lt_typein (r : α -> α -> Prop) [IsWellO
rder α r] {a b : α} : typein r a < typein r b ↔ r a b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
-/
theorem unbounded_range_of_le_iSup {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ ⨆ i, typein r (f i)) : Unbounded r (range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
    h.not_gt <| lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)
/-
**Ordinal.sSup_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sSup_ord (s : Set Cardinal) : (sSup s).ord = sSup (ord '' s)
参数：s : Set Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Cardinal.ord_zero`：ord_zero : ord 0 = 0
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsNormal.map_sSup`：map_sSup (hf : IsNormal f) {s : Set α} (hs : s.
Nonempty) (hs' : BddAbove s) : f (sSup s) = sSup (f '' s)
· 使用定理 `Cardinal.isNormal_ord`：isNormal_ord : Order.IsNormal ord where strictMon
o
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Cardinal.bddAbove_ord_image_iff`：bddAbove_ord_image_iff {s : Set Cardina
l} : BddAbove (ord '' s) ↔ BddAbove s
-/
theorem sSup_ord (s : Set Cardinal) : (sSup s).ord = sSup (ord '' s) := by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · simp
  · by_cases hs : BddAbove s
    · exact isNormal_ord.map_sSup hn hs
    · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (bddAbove_ord_image_iff.not.2 hs)]
      simp
/-
**Ordinal.iSup_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_ord {ι} (f : ι -> Cardinal) : (⨆ i, f i).ord = ⨆ i, (f i).ord
参数：f : ι -> Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Ordinal.sSup_ord`：sSup_ord (s : Set Cardinal) : (sSup s).ord = sSup (ord
 '' s)
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
-/
theorem iSup_ord {ι} (f : ι → Cardinal) : (⨆ i, f i).ord = ⨆ i, (f i).ord := by
  rw [iSup, iSup, sSup_ord, range_comp']
/-
**Ordinal.lift_card_sInf_compl_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_card_sInf_compl_le (s : Set Ordinal.{u}) : Cardinal.lift.{u + 1} (sIn
f sᶜ).card <= #s
参数：s : Set Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.not_notMem`：not_notMem : ¬a ∉ s ↔ a in s
· 使用定理 `notMem_of_lt_csInf'`：notMem_of_lt_csInf' {x : α} {s : Set α} (h : x < sI
nf s) : x ∉ s
-/
theorem lift_card_sInf_compl_le (s : Set Ordinal.{u}) :
    Cardinal.lift.{u + 1} (sInf sᶜ).card ≤ #s := by
  rw [← Cardinal.mk_Iio_ordinal]
  refine mk_le_mk_of_subset fun x (hx : x < _) ↦ ?_
  rw [← not_notMem]
  exact notMem_of_lt_csInf' hx
/-
**Ordinal.card_sInf_range_compl_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_sInf_range_compl_le_lift {ι : Type u} (f : ι -> Ordinal.{max u v}) : 
(sInf (range f)ᶜ).card <= Cardinal.lift.{v} #ι
参数：f : ι -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.lift_card_sInf_compl_le`：lift_card_sInf_compl_le (s : Set Ordina
l.{u}) : Cardinal.lift.{u + 1} (sInf sᶜ).card <= #s
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
-/
theorem card_sInf_range_compl_le_lift {ι : Type u} (f : ι → Ordinal.{max u v}) :
    (sInf (range f)ᶜ).card ≤ Cardinal.lift.{v} #ι := by
  rw [← Cardinal.lift_le.{max u v + 1}, Cardinal.lift_lift]
  apply (lift_card_sInf_compl_le _).trans
  rw [← Cardinal.lift_id'.{u, max u v + 1} #(range _)]
  exact mk_range_le_lift
/-
**Ordinal.card_sInf_range_compl_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_sInf_range_compl_le {ι : Type u} (f : ι -> Ordinal.{u}) : (sInf (rang
e f)ᶜ).card <= #ι
参数：f : ι -> Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_sInf_range_compl_le_lift`：card_sInf_range_compl_le_lift {ι 
: Type u} (f : ι -> Ordinal.{max u v}) : (sInf (range f)ᶜ).card <= Cardinal.lift
.{v} #ι
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem card_sInf_range_compl_le {ι : Type u} (f : ι → Ordinal.{u}) :
    (sInf (range f)ᶜ).card ≤ #ι :=
  Cardinal.lift_id #ι ▸ card_sInf_range_compl_le_lift f
/-
**Ordinal.sInf_compl_lt_lift_ord_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sInf_compl_lt_lift_ord_succ {ι : Type u} (f : ι -> Ordinal.{max u v}) : sI
nf (range f)ᶜ < lift.{v} (succ #ι).ord
参数：f : ι -> Ordinal.{max u v}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_ord`：lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lif
t.{u, v} c)
· 使用定理 `Cardinal.lift_succ`：lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v
, u} a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.card_le_iff`：card_le_iff {o : Ordinal} {c : Cardinal} : o.card 
<= c ↔ o < (succ c).ord
· 使用定理 `Ordinal.card_sInf_range_compl_le_lift`：card_sInf_range_compl_le_lift {ι 
: Type u} (f : ι -> Ordinal.{max u v}) : (sInf (range f)ᶜ).card <= Cardinal.lift
.{v} #ι
-/
theorem sInf_compl_lt_lift_ord_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sInf (range f)ᶜ < lift.{v} (succ #ι).ord := by
  rw [lift_ord, Cardinal.lift_succ, ← card_le_iff]
  exact card_sInf_range_compl_le_lift f
/-
**Ordinal.sInf_compl_lt_ord_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sInf_compl_lt_ord_succ {ι : Type u} (f : ι -> Ordinal.{u}) : sInf (range f
)ᶜ < (succ #ι).ord
参数：f : ι -> Ordinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.sInf_compl_lt_lift_ord_succ`：sInf_compl_lt_lift_ord_succ {ι : Ty
pe u} (f : ι -> Ordinal.{max u v}) : sInf (range f)ᶜ < lift.{v} (succ #ι).ord
· 使用定理 `Ordinal.lift_id`：lift_id : forall a, lift.{u, u} a = a
-/
theorem sInf_compl_lt_ord_succ {ι : Type u} (f : ι → Ordinal.{u}) :
    sInf (range f)ᶜ < (succ #ι).ord :=
  lift_id (succ #ι).ord ▸ sInf_compl_lt_lift_ord_succ f
/-
**Ordinal.bddAbove_add_one_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_add_one_image_iff {s : Set Ordinal} : BddAbove ((· + 1) '' s) ↔ B
ddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem bddAbove_add_one_image_iff {s : Set Ordinal} :
    BddAbove ((· + 1) '' s) ↔ BddAbove s := by
  constructor <;> rintro ⟨a, ha⟩
  · exact ⟨a, fun b hb ↦ (lt_add_one _).le.trans (ha (mem_image_of_mem _ hb))⟩
  · use a + 1
    simpa [upperBounds]
/-
**Ordinal.bddAbove_range_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bddAbove_range_add_one_iff {f : β -> Ordinal.{u}} : BddAbove (range fun i 
=> f i + 1) ↔ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `Ordinal.bddAbove_add_one_image_iff`：bddAbove_add_one_image_iff {s : Set 
Ordinal} : BddAbove ((· + 1) '' s) ↔ BddAbove s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bddAbove_range_add_one_iff {f : β → Ordinal.{u}} :
    BddAbove (range fun i ↦ f i + 1) ↔ BddAbove (range f) := by
  rw [range_comp' (· + 1), bddAbove_add_one_image_iff]
/-
**Ordinal.sSup_le_sSup_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sSup_le_sSup_add_one (s : Set Ordinal) : sSup s <= sSup ((· + 1) '' s)
参数：s : Set Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.bddAbove_add_one_image_iff`：bddAbove_add_one_image_iff {s : Set 
Ordinal} : BddAbove ((· + 1) '' s) ↔ BddAbove s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_le_iff'`：csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSu
p s <= a ↔ forall x in s, x <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem sSup_le_sSup_add_one (s : Set Ordinal) : sSup s ≤ sSup ((· + 1) '' s) := by
  by_cases hs : BddAbove s
  · have hs' := bddAbove_add_one_image_iff.2 hs
    rw [csSup_le_iff' hs]
    exact fun x hx ↦ (lt_add_one _).le.trans (le_csSup hs' (mem_image_of_mem _ hx))
  · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := _ '' _)]
    rwa [bddAbove_add_one_image_iff]
/-
**Ordinal.iSup_le_iSup_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_le_iSup_add_one (f : β -> Ordinal) : ⨆ i, f i <= ⨆ i, f i + 1
参数：f : β -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `Ordinal.sSup_le_sSup_add_one`：sSup_le_sSup_add_one (s : Set Ordinal) : s
Sup s <= sSup ((· + 1) '' s)
-/
theorem iSup_le_iSup_add_one (f : β → Ordinal) : ⨆ i, f i ≤ ⨆ i, f i + 1 := by
  rw [iSup, iSup, range_comp' (· + 1)]
  exact sSup_le_sSup_add_one _
/-
**Ordinal.iSup_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_add_one {β : Type*} [LinearOrder β] [NoMaxOrder β] {f : β -> Ordinal.
{u}} (hf : StrictMono f) : ⨆ i, f i + 1 = ⨆ i, f i
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Ordinal.iSup_le_iSup_add_one`：iSup_le_iSup_add_one (f : β -> Ordinal) : 
⨆ i, f i <= ⨆ i, f i + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.bddAbove_range_add_one_iff`：bddAbove_range_add_one_iff {f : β ->
 Ordinal.{u}} : BddAbove (range fun i => f i + 1) ↔ BddAbove (range f)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Order.add_one_le_iff`：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem iSup_add_one {β : Type*} [LinearOrder β] [NoMaxOrder β]
    {f : β → Ordinal.{u}} (hf : StrictMono f) : ⨆ i, f i + 1 = ⨆ i, f i := by
  apply (iSup_le_iSup_add_one f).antisymm'
  by_cases hf' : BddAbove (range f)
  · rw [ciSup_le_iff' (bddAbove_range_add_one_iff.2 hf')]
    intro i
    obtain ⟨j, hj⟩ := exists_gt i
    apply (le_ciSup hf' j).trans'
    rw [add_one_le_iff]
    exact hf hj
  · rw [ciSup_of_not_bddAbove hf', ciSup_of_not_bddAbove]
    rwa [← bddAbove_range_add_one_iff] at hf'
/-
**Ordinal.iSup_Iio_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_Iio_add_one {a : Ordinal.{u}} {f : Iio a -> Ordinal.{u}} (hf : Strict
Mono f) (ha : IsSuccPrelimit a) : ⨆ i : Iio a, f i + 1 = ⨆ i : Iio a, f i
参数：hf : StrictMono f；ha : IsSuccPrelimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.noMaxOrder_Iio`：∀ {α : Type u_1} {a : α} [inst : Pr
eorder α], Order.IsSuccPrelimit a → NoMaxOrder ↑(Set.Iio a)
· 使用定理 `Ordinal.iSup_add_one`：iSup_add_one {β : Type*} [LinearOrder β] [NoMaxOrd
er β] {f : β -> Ordinal.{u}} (hf : StrictMono f) : ⨆ i, f i + 1 = ⨆ i, f i
-/
theorem iSup_Iio_add_one {a : Ordinal.{u}} {f : Iio a → Ordinal.{u}}
    (hf : StrictMono f) (ha : IsSuccPrelimit a) : ⨆ i : Iio a, f i + 1 = ⨆ i : Iio a, f i := by
  have := ha.noMaxOrder_Iio
  exact iSup_add_one hf

section bsup

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/-
**Ordinal.iSup_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_iSup {ι ι' : Type u} (r : ι -> ι -> Prop) (r' : ι' -> ι' -> Prop) 
[IsWellOrder ι r] [IsWellOrder ι' r'] {o : Ordinal} (ho : type r = o) (ho' : typ
e r' = o) (f : forall a < o, Ordinal) : iSup (familyOfBFamily' r ho f) = iSup (f
amilyOfBFamily' r' ho' f)
参数：r : ι -> ι -> Prop；r' : ι' -> ι' -> Prop；ho : type r = o；ho' : type r' = o；f 
: forall a < o, Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.range_familyOfBFamily'`：range_familyOfBFamily' {ι : Type u} (r :
 ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho : type r = o) (f : forall a < o, α) :
 range (familyOfBFam…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_eq_iSup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o : Ordinal} (ho : type r = o) (ho' : type r' = o) (f : ∀ a < o, Ordinal) :
    iSup (familyOfBFamily' r ho f) = iSup (familyOfBFamily' r' ho' f) :=
  congrArg sSup (by simp_rw [range_familyOfBFamily'])

/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
`o : Ordinal.{u}`. This is a special case of `iSup` over the family provided by
`familyOfBFamily`. -/
@[deprecated "write `⨆ i : Iio a, f i` instead." (since := "2026-04-05")]
/-
**Ordinal.bsup** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：bsup (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v}) : Ordinal.{ma
x u v}
参数：o : Ordinal.{u}；f : forall a < o, Ordinal.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of a family of ordinals indexed by the set of ordinals less than so
me
`o : Ordinal.{u}`. This is a special case of `iSup` over the family provided by
`familyOfBFamily`.
-/
def bsup (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup (familyOfBFamily o f)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.iSup_eq_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordinal) : iSup (familyOfBFa
mily o f) = bsup o f
参数：f : forall a < o, Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup_eq_bsup {o : Ordinal} (f : ∀ a < o, Ordinal) :
    iSup (familyOfBFamily o f) = bsup o f :=
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.iSup'_eq_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {o : Ordinal.{u_3}} {ι : Type u_3} (r : ι → ι → Prop) [inst : IsWellOrde
r ι r] (ho : Ordinal.type r = o)   (f : (a : Ordinal.{u_3}) → a < o → Ordinal.{m
ax u_3 u_4}), iSup (Ordinal.familyOfBFamily' r ho f) = o.bsup f
参数：r : ι → ι → Prop；ho : Ordinal.type r = o；f : (a : Ordinal.{u_3}) → a < o → Or
dinal.{max u_3 u_4}；Ordinal.familyOfBFamily' r ho f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_eq_iSup`：iSup_eq_iSup {ι ι' : Type u} (r : ι -> ι -> Prop) 
(r' : ι' -> ι' -> Prop) [IsWellOrder ι r] [IsWellOrder ι' r'] {o : Ordinal} (ho 
: type r =…
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem iSup'_eq_bsup {o : Ordinal} {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (ho : type r = o)
    (f : ∀ a < o, Ordinal) : iSup (familyOfBFamily' r ho f) = bsup o f :=
  iSup_eq_iSup r _ ho _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.sSup_eq_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordinal) : sSup (brange o f)
 = bsup o f
参数：f : forall a < o, Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.range_familyOfBFamily`：range_familyOfBFamily {o} (f : forall a <
 o, α) : range (familyOfBFamily o f) = brange o f
-/
theorem sSup_eq_bsup {o : Ordinal} (f : ∀ a < o, Ordinal) : sSup (brange o f) = bsup o f := by
  congr
  rw [range_familyOfBFamily]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup'_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {ι : Type u_3} (r : ι → ι → Prop) [inst : IsWellOrder ι r] (f : ι → Ordi
nal.{max u_3 u_4}),   (Ordinal.type r).bsup (Ordinal.bfamilyOfFamily' r f) = iSu
p f
参数：r : ι → ι → Prop；f : ι → Ordinal.{max u_3 u_4}；Ordinal.type r；Ordinal.bfamily
OfFamily' r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup'_eq_bsup`：∀ {o : Ordinal.{u_3}} {ι : Type u_3} (r : ι → ι →
 Prop) [inst : IsWellOrder ι r] (ho : Ordinal.type r = o)   (f : (a : Ordinal.{u
_3}) → a < …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
-/
theorem bsup'_eq_iSup {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal) :
    bsup _ (bfamilyOfFamily' r f) = iSup f := by
  simp +unfoldPartialApp only [← iSup'_eq_bsup r, enum_typein, familyOfBFamily', bfamilyOfFamily']

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_iSup {ι} (f : ι -> Ordinal) : bsup _ (bfamilyOfFamily f) = iSup f
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup'_eq_iSup`：∀ {ι : Type u_3} (r : ι → ι → Prop) [inst : IsWel
lOrder ι r] (f : ι → Ordinal.{max u_3 u_4}),   (Ordinal.type r).bsup (Ordinal.bf
amilyOfFami…
-/
theorem bsup_eq_iSup {ι} (f : ι → Ordinal) : bsup _ (bfamilyOfFamily f) = iSup f :=
  bsup'_eq_iSup _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_eq_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_bsup {ι : Type u} (r r' : ι -> ι -> Prop) [IsWellOrder ι r] [IsWel
lOrder ι r'] (f : ι -> Ordinal.{max u v}) : bsup.{_, v} _ (bfamilyOfFamily' r f)
 = bsup.{_, v} _ (bfamilyOfFamily' r' f)
参数：r r' : ι -> ι -> Prop；f : ι -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.bsup'_eq_iSup`：∀ {ι : Type u_3} (r : ι → ι → Prop) [inst : IsWel
lOrder ι r] (f : ι → Ordinal.{max u_3 u_4}),   (Ordinal.type r).bsup (Ordinal.bf
amilyOfFami…
-/
theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = bsup.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [bsup'_eq_iSup, bsup'_eq_iSup]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_congr** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_congr {o₁ o₂ : Ordinal.{u}} (f : forall a < o₁, Ordinal.{max u v}) (h
o : o₁ = o₂) : bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.s
ymm)
参数：f : forall a < o₁, Ordinal.{max u v}；ho : o₁ = o₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bsup_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_le_iff {o f a} : bsup.{u, v} o f <= a ↔ forall i h, f i h <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.familyOfBFamily_enum`：familyOfBFamily_enum (o : Ordinal) (f : fo
rall a < o, α) (i hi) : familyOfBFamily o f (enum (α
-/
theorem bsup_le_iff {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  Ordinal.iSup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} : (forall i h, f i h
 <= a) -> bsup.{u, v} o f <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.bsup_le_iff`：bsup_le_iff {o f a} : bsup.{u, v} o f <= a ↔ forall
 i h, f i h <= a
-/
theorem bsup_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} :
    (∀ i h, f i h ≤ a) → bsup.{u, v} o f ≤ a :=
  bsup_le_iff.2

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.le_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <= bsup o f
参数：f : forall a < o, Ordinal；i h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.bsup_le_iff`：bsup_le_iff {o f a} : bsup.{u, v} o f <= a ↔ forall
 i h, f i h <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_bsup {o} (f : ∀ a < o, Ordinal) (i h) : f i h ≤ bsup o f :=
  bsup_le_iff.1 le_rfl _ _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.lt_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_bsup {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) {a} : a < 
bsup.{_, v} o f ↔ exists i hi, a < f i hi
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.bsup_le_iff`：bsup_le_iff {o f a} : bsup.{u, v} o f <= a ↔ forall
 i h, f i h <= a
-/
theorem lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {a} :
    a < bsup.{_, v} o f ↔ ∃ i hi, a < f i hi := by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

@[deprecated IsNormal.map_iSup (since := "2026-04-05")]
/-
**Ordinal.IsNormal.bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsNormal`。
形式化陈述：∀ {f : Ordinal.{max u_3 u_4} → Ordinal.{max u_4 u_5}},   Order.IsNormal f 
→     ∀ {o : Ordinal.{u_4}} (g : (a : Ordinal.{u_4}) → a < o → Ordinal.{max u_4 
u_3}),       o ≠ 0 → f (o.bsup g) = o.bsup fun a h => f (g a h)
参数：g : (a : Ordinal.{u_4}) → a < o → Ordinal.{max u_4 u_3}；o.bsup g；g a h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.type_ne_zero_iff_nonempty`：type_ne_zero_iff_nonempty [IsWellOrde
r α r] : type r != 0 ↔ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup'_eq_bsup`：∀ {o : Ordinal.{u_3}} {ι : Type u_3} (r : ι → ι →
 Prop) [inst : IsWellOrder ι r] (ho : Ordinal.type r = o)   (f : (a : Ordinal.{u
_3}) → a < …
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem IsNormal.bsup {f : Ordinal → Ordinal} (H : IsNormal f) {o : Ordinal} :
    ∀ (g : ∀ a < o, Ordinal), o ≠ 0 → f (bsup o g) = bsup o fun a h => f (g a h) :=
  inductionOn o fun α r _ g h => by
    have := type_ne_zero_iff_nonempty.1 h
    rw [← iSup'_eq_bsup r, Order.IsNormal.map_iSup H bddAbove_of_small, ← iSup'_eq_bsup r] <;>
      rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.lt_bsup_of_ne_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}}
 : (forall i h, f i h != bsup.{_, v} o f) ↔ forall i h, f i h < bsup.{_, v} o f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} :
    (∀ i h, f i h ≠ bsup.{_, v} o f) ↔ ∀ i h, f i h < bsup.{_, v} o f :=
  ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_not_succ_of_ne_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max
 u v}} (hf : forall {i : Ordinal} (h : i < o), f i h != bsup.{_, v} o f) (a) : a
 < bsup.{_, v} o f -> succ a < bsup.{_, v} o f
参数：hf : forall {i : Ordinal} (h : i < o), f i h != bsup.{_, v} o f；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_eq_bsup`：iSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordi
nal) : iSup (familyOfBFamily o f) = bsup o f
· 使用定理 `Ordinal.succ_lt_iSup_of_ne_iSup`：succ_lt_iSup_of_ne_iSup {ι} {f : ι -> O
rdinal.{u}} [Small.{u} ι] (hf : forall i, f i != iSup f) {a} (hao : a < iSup f) 
: succ a < iSup f
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}}
    (hf : ∀ {i : Ordinal} (h : i < o), f i h ≠ bsup.{_, v} o f) (a) :
    a < bsup.{_, v} o f → succ a < bsup.{_, v} o f := by
  rw [← iSup_eq_bsup] at *
  exact succ_lt_iSup_of_ne_iSup fun i => hf _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_zero_iff {o} {f : forall a < o, Ordinal} : bsup o f = 0 ↔ forall i
 hi, f i hi = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.bsup_le`：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
 (forall i h, f i h <= a) -> bsup.{u, v} o f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
-/
theorem bsup_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 := by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => nonpos_iff_eq_zero.2 (h i hi)) zero_le⟩
  rw [← nonpos_iff_eq_zero, ← h]
  exact le_bsup f i hi

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.lt_bsup_of_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_bsup_of_limit {o : Ordinal} {f : forall a < o, Ordinal} (hf : forall {a
 a'} (ha : a < o) (ha' : a' < o), a < a' -> f a ha < f a' ha') (ho : forall a < 
o, succ a < o) (i h) : f i h < bsup o f
参数：hf : forall {a a'} (ha : a < o) (ha' : a' < o), a < a' -> f a ha < f a' ha'；h
o : forall a < o, succ a < o；i h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
-/
theorem lt_bsup_of_limit {o : Ordinal} {f : ∀ a < o, Ordinal}
    (hf : ∀ {a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
    (ho : ∀ a < o, succ a < o) (i h) : f i h < bsup o f :=
  (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_succ_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_succ_of_mono {o : Ordinal} {f : forall a < succ o, Ordinal} (hf : for
all {i j} (hi hj), i <= j -> f i hi <= f j hj) : bsup _ f = f o (lt_succ o)
参数：hf : forall {i j} (hi hj), i <= j -> f i hi <= f j hj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.bsup_le`：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
 (forall i h, f i h <= a) -> bsup.{u, v} o f <= a
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
-/
theorem bsup_succ_of_mono {o : Ordinal} {f : ∀ a < succ o, Ordinal}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : bsup _ f = f o (lt_succ o) :=
  le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_zero (f : forall a < (0 : Ordinal), Ordinal) : bsup 0 f = 0
参数：f : forall a < (0 : Ordinal), Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.bsup_eq_zero_iff`：bsup_eq_zero_iff {o} {f : forall a < o, Ordina
l} : bsup o f = 0 ↔ forall i hi, f i hi = 0
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem bsup_zero (f : ∀ a < (0 : Ordinal), Ordinal) : bsup 0 f = 0 :=
  bsup_eq_zero_iff.2 fun _i hi => (not_lt_zero hi).elim

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_const** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_const {o : Ordinal.{u}} (ho : o != 0) (a : Ordinal.{max u v}) : (bsup
.{_, v} o fun _ _ => a) = a
参数：ho : o != 0；a : Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.bsup_le`：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
 (forall i h, f i h <= a) -> bsup.{u, v} o f <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem bsup_const {o : Ordinal.{u}} (ho : o ≠ 0) (a : Ordinal.{max u v}) :
    (bsup.{_, v} o fun _ _ => a) = a :=
  le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (pos_iff_ne_zero.2 ho))

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_one (f : forall a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_
one
参数：f : forall a < (1 : Ordinal), Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.typein_one_toType`：typein_one_toType (x : ToType 1) : typein (α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bsup_one (f : ∀ a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_one := by
  simp_rw [← iSup_eq_bsup, ciSup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_le_of_brange_subset** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_le_of_brange_subset {o o'} {f : forall a < o, Ordinal} {g : forall a 
< o', Ordinal} (h : brange o f subseteq brange o' g) : bsup.{u, max v w} o f <= 
bsup.{v, max u w} o' g
参数：h : brange o f subseteq brange o' g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_le`：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
 (forall i h, f i h <= a) -> bsup.{u, v} o f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
-/
theorem bsup_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : bsup.{u, max v w} o f ≤ bsup.{v, max u w} o' g :=
  bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.bsup_eq_of_brange_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_of_brange_eq {o o'} {f : forall a < o, Ordinal} {g : forall a < o'
, Ordinal} (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max
 u w} o' g
参数：h : brange o f = brange o' g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.bsup_le_of_brange_subset`：bsup_le_of_brange_subset {o o'} {f : f
orall a < o, Ordinal} {g : forall a < o', Ordinal} (h : brange o f subseteq bran
ge o' g) : bsup.{u, ma…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem bsup_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g :=
  (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/-
**Ordinal.iSup_Iio_eq_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_Iio_eq_bsup {o} {f : forall a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 
= bsup o f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.range_familyOfBFamily`：range_familyOfBFamily {o} (f : forall a <
 o, α) : range (familyOfBFamily o f) = brange o f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_Iio_eq_bsup {o} {f : ∀ a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 = bsup o f := by
  simp_rw [Iio, bsup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_ofPred]

end bsup

section lsub

/-- The least strict upper bound of a family of ordinals. -/
@[deprecated "write `⨆ i, f i + 1` instead." (since := "2026-03-27")]
/-
**Ordinal.lsub** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：lsub {ι : Type u} (f : ι -> Ordinal.{max u v}) : Ordinal
参数：f : ι -> Ordinal.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The least strict upper bound of a family of ordinals.
-/
def lsub {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal :=
  iSup (succ ∘ f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.iSup_eq_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_lsub {ι} (f : ι -> Ordinal) : iSup (succ ∘ f) = lsub f
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup_eq_lsub {ι} (f : ι → Ordinal) : iSup (succ ∘ f) = lsub f :=
  rfl

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= a ↔ forall i, f i < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_add_one_le_iff`：iSup_add_one_le_iff {ι} {f : ι -> Ordinal.{
u}} {a : Ordinal.{u}} [Small.{u} ι] : ⨆ i, f i + 1 <= a ↔ forall i, f i < a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem lsub_le_iff {ι} {f : ι → Ordinal} {a} : lsub f ≤ a ↔ ∀ i, f i < a :=
  Ordinal.iSup_add_one_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a) -> lsub f <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.lsub_le_iff`：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= 
a ↔ forall i, f i < a
-/
theorem lsub_le {ι} {f : ι → Ordinal} {a} : (∀ i, f i < a) → lsub f ≤ a :=
  lsub_le_iff.2

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lt_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
参数：f : ι -> Ordinal；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lt_iSup_add_one`：lt_iSup_add_one {ι} (f : ι -> Ordinal.{u}) [Sma
ll.{u} ι] (i) : f i < ⨆ i, f i + 1
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem lt_lsub {ι} (f : ι → Ordinal) (i) : f i < lsub f :=
  Ordinal.lt_iSup_add_one f i

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lt_lsub_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_lsub_iff {ι} {f : ι -> Ordinal} {a} : a < lsub f ↔ exists i, a <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.lsub_le_iff`：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= 
a ↔ forall i, f i < a
-/
theorem lt_lsub_iff {ι} {f : ι → Ordinal} {a} : a < lsub f ↔ ∃ i, a ≤ f i := by
  simpa only [not_forall, not_lt, not_le] using not_congr lsub_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.iSup_le_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_le_lsub {ι} (f : ι -> Ordinal) : iSup f <= lsub f
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
-/
theorem iSup_le_lsub {ι} (f : ι → Ordinal) : iSup f ≤ lsub f :=
  Ordinal.iSup_le fun i => (lt_lsub f i).le

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_le_succ_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_le_succ_iSup {ι} (f : ι -> Ordinal) : lsub f <= succ (iSup f)
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lsub_le`：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a
) -> lsub f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem lsub_le_succ_iSup {ι} (f : ι → Ordinal) : lsub f ≤ succ (iSup f) :=
  lsub_le fun i => lt_succ_iff.2 (Ordinal.le_iSup f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.iSup_eq_lsub_or_succ_iSup_eq_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_lsub_or_succ_iSup_eq_lsub {ι} (f : ι -> Ordinal) : iSup f = lsub f
 ∨ succ (iSup f) = lsub f
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Ordinal.iSup_le_lsub`：iSup_le_lsub {ι} (f : ι -> Ordinal) : iSup f <= ls
ub f
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Ordinal.lsub_le_succ_iSup`：lsub_le_succ_iSup {ι} (f : ι -> Ordinal) : ls
ub f <= succ (iSup f)
-/
theorem iSup_eq_lsub_or_succ_iSup_eq_lsub {ι} (f : ι → Ordinal) :
    iSup f = lsub f ∨ succ (iSup f) = lsub f := by
  rcases eq_or_lt_of_le (iSup_le_lsub f) with h | h
  · exact Or.inl h
  · exact Or.inr ((succ_le_of_lt h).antisymm (lsub_le_succ_iSup f))

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.succ_iSup_le_lsub_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_iSup_le_lsub_iff {ι} (f : ι -> Ordinal) : succ (iSup f) <= lsub f ↔ e
xists i, f i = iSup f
参数：f : ι -> Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.iSup_le_lsub`：iSup_le_lsub {ι} (f : ι -> Ordinal) : iSup f <= ls
ub f
· 使用定理 `Ordinal.lsub_le`：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a
) -> lsub f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
-/
theorem succ_iSup_le_lsub_iff {ι} (f : ι → Ordinal) :
    succ (iSup f) ≤ lsub f ↔ ∃ i, f i = iSup f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    have := forall_congr' fun i ↦ (Ordinal.le_iSup f i).lt_iff_ne.symm
    exact (succ_le_iff.1 h).ne ((iSup_le_lsub f).antisymm (lsub_le (this.1 hf)))
  rintro ⟨_, hf⟩
  rw [succ_le_iff, ← hf]
  exact lt_lsub _ _

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.succ_iSup_eq_lsub_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_iSup_eq_lsub_iff {ι} (f : ι -> Ordinal) : succ (iSup f) = lsub f ↔ ex
ists i, f i = iSup f
参数：f : ι -> Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Ordinal.lsub_le_succ_iSup`：lsub_le_succ_iSup {ι} (f : ι -> Ordinal) : ls
ub f <= succ (iSup f)
· 使用定理 `Ordinal.succ_iSup_le_lsub_iff`：succ_iSup_le_lsub_iff {ι} (f : ι -> Ordin
al) : succ (iSup f) <= lsub f ↔ exists i, f i = iSup f
-/
theorem succ_iSup_eq_lsub_iff {ι} (f : ι → Ordinal) :
    succ (iSup f) = lsub f ↔ ∃ i, f i = iSup f :=
  (lsub_le_succ_iSup f).ge_iff_eq'.symm.trans (succ_iSup_le_lsub_iff f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.iSup_eq_lsub_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_lsub_iff {ι} (f : ι -> Ordinal) : iSup f = lsub f ↔ forall a < lsu
b f, succ a < lsub f
参数：f : ι -> Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.succ_lt_iSup_of_ne_iSup`：succ_lt_iSup_of_ne_iSup {ι} {f : ι -> O
rdinal.{u}} [Small.{u} ι] (hf : forall i, f i != iSup f) {a} (hao : a < iSup f) 
: succ a < iSup f
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lsub_le_iff`：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= 
a ↔ forall i, f i < a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.iSup_le_lsub`：iSup_le_lsub {ι} (f : ι -> Ordinal) : iSup f <= ls
ub f
· 使用定理 `Ordinal.lsub_le`：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a
) -> lsub f <= a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.succ_iSup_eq_lsub_iff`：succ_iSup_eq_lsub_iff {ι} (f : ι -> Ordin
al) : succ (iSup f) = lsub f ↔ exists i, f i = iSup f
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
-/
theorem iSup_eq_lsub_iff {ι} (f : ι → Ordinal) :
    iSup f = lsub f ↔ ∀ a < lsub f, succ a < lsub f := by
  refine ⟨fun h => ?_, fun hf => le_antisymm (iSup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => succ_lt_iSup_of_ne_iSup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (succ_iSup_eq_lsub_iff f).2 ⟨i, le_antisymm (Ordinal.le_iSup _ _) hle⟩
  have :=
    hf _
      (by
        rw [← heq]
        exact lt_succ (iSup f))
  rw [heq] at this
  exact this.false

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.iSup_eq_lsub_iff_lt_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_eq_lsub_iff_lt_iSup {ι} (f : ι -> Ordinal) : iSup f = lsub f ↔ forall
 i, f i < iSup f
参数：f : ι -> Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.iSup_le_lsub`：iSup_le_lsub {ι} (f : ι -> Ordinal) : iSup f <= ls
ub f
· 使用定理 `Ordinal.lsub_le`：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a
) -> lsub f <= a
-/
theorem iSup_eq_lsub_iff_lt_iSup {ι} (f : ι → Ordinal) :
    iSup f = lsub f ↔ ∀ i, f i < iSup f :=
  ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymm (iSup_le_lsub f) (lsub_le h)⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_empty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_empty {ι} [h : IsEmpty ι] (f : ι -> Ordinal) : lsub f = 0
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.lsub_le_iff`：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= 
a ↔ forall i, f i < a
-/
theorem lsub_empty {ι} [h : IsEmpty ι] (f : ι → Ordinal) : lsub f = 0 := by
  rw [← nonpos_iff_eq_zero, lsub_le_iff]
  exact h.elim

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_pos {ι} [h : Nonempty ι] (f : ι -> Ordinal) : 0 < lsub f
参数：f : ι -> Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
-/
theorem lsub_pos {ι} [h : Nonempty ι] (f : ι → Ordinal) : 0 < lsub f :=
  h.elim fun i => (lt_lsub f i).pos

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_eq_zero_iff {ι} (f : ι -> Ordinal) : lsub.{_, v} f = 0 ↔ IsEmpty ι
参数：f : ι -> Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lsub_pos`：lsub_pos {ι} [h : Nonempty ι] (f : ι -> Ordinal) : 0 <
 lsub f
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lsub_empty`：lsub_empty {ι} [h : IsEmpty ι] (f : ι -> Ordinal) : 
lsub f = 0
-/
theorem lsub_eq_zero_iff {ι} (f : ι → Ordinal) :
    lsub.{_, v} f = 0 ↔ IsEmpty ι := by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos.{_, v} _ ⟨i⟩ f
  rw [h] at this
  exact this.false

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_const** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_const {ι} [Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = succ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
-/
theorem lsub_const {ι} [Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = succ o :=
  ciSup_const

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_unique** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_unique {ι} [Unique ι] (f : ι -> Ordinal) : lsub f = succ (f default)
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
-/
theorem lsub_unique {ι} [Unique ι] (f : ι → Ordinal) : lsub f = succ (f default) :=
  ciSup_unique

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_le_of_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_le_of_range_subset {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal} (h :
 Set.range f subseteq Set.range g) : lsub.{u, max v w} f <= lsub.{v, max u w} g
参数：h : Set.range f subseteq Set.range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le_csSup'`：csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s
 subseteq t) : sSup s <= sSup t
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem lsub_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f ⊆ Set.range g) : lsub.{u, max v w} f ≤ lsub.{v, max u w} g :=
  csSup_le_csSup' bddAbove_of_small (by convert! Set.image_mono h <;> apply Set.range_comp)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_eq_of_range_eq {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal} (h : Set
.range f = Set.range g) : lsub.{u, max v w} f = lsub.{v, max u w} g
参数：h : Set.range f = Set.range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.lsub_le_of_range_subset`：lsub_le_of_range_subset {ι ι'} {f : ι -
> Ordinal} {g : ι' -> Ordinal} (h : Set.range f subseteq Set.range g) : lsub.{u,
 max v w} f <= lsub.{…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem lsub_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : lsub.{u, max v w} f = lsub.{v, max u w} g :=
  (lsub_le_of_range_subset.{u, v, w} h.le).antisymm (lsub_le_of_range_subset.{v, u, w} h.ge)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_sum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_sum {α : Type u} {β : Type v} (f : α oplus β -> Ordinal) : lsub.{max 
u v, w} f = max (lsub.{u, max v w} fun a => f (Sum.inl a)) (lsub.{v, max u w} fu
n b => f (Sum.inr b))
参数：f : α oplus β -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_sum`：iSup_sum {α β} (f : α oplus β -> Ordinal.{u}) [Small.{
u} α] [Small.{u} β] : iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b))
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem lsub_sum {α : Type u} {β : Type v} (f : α ⊕ β → Ordinal) :
    lsub.{max u v, w} f =
      max (lsub.{u, max v w} fun a => f (Sum.inl a)) (lsub.{v, max u w} fun b => f (Sum.inr b)) :=
  iSup_sum _

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_notMem_range {ι} (f : ι -> Ordinal) : lsub f ∉ Set.range f
参数：f : ι -> Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
-/
theorem lsub_notMem_range {ι} (f : ι → Ordinal) :
    lsub f ∉ Set.range f := fun ⟨i, h⟩ =>
  h.not_lt (lt_lsub f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.nonempty_compl_range** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nonempty_compl_range {ι : Type u} (f : ι -> Ordinal.{max u v}) : (Set.rang
e f)ᶜ.Nonempty
参数：f : ι -> Ordinal.{max u v}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lsub_notMem_range`：lsub_notMem_range {ι} (f : ι -> Ordinal) : ls
ub f ∉ Set.range f
-/
theorem nonempty_compl_range {ι : Type u} (f : ι → Ordinal.{max u v}) : (Set.range f)ᶜ.Nonempty :=
  ⟨_, lsub_notMem_range f⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/-
**Ordinal.lsub_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.lsub_le`：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a
) -> lsub f <= a
· 使用定理 `Ordinal.typein_lt_self`：typein_lt_self {o : Ordinal} (i : o.ToType) : ty
pein (α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
-/
theorem lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α := o.ToType) (· < ·)) = o :=
  (lsub_le.{u, u} typein_lt_self).antisymm
    (by
      by_contra! h
      have h := h.trans_eq (type_toType o).symm
      simpa [typein_enum] using lt_lsub.{u, u} (typein (· < ·)) (enum (· < ·) ⟨_, h⟩))

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-27")]
/-
**Ordinal.iSup_typein_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_typein_limit {o : Ordinal.{u}} (ho : forall a, a < o -> succ a < o) :
 iSup (typein ((· < ·) : o.ToType -> o.ToType -> Prop)) = o
参数：ho : forall a, a < o -> succ a < o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccPrelimit_iff_succ_lt`：isSuccPrelimit_iff_succ_lt : IsSuccPre
limit b ↔ forall a < b, succ a < b
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `PrincipalSeg.range_eq`：range_eq (f : r ≺i s) : Set.range f = {b | s b f.
top}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Order.IsSuccPrelimit.sSup_Iio`：Order.IsSuccPrelimit.sSup_Iio (h : IsSucc
Prelimit x) : sSup (Iio x) = x
-/
theorem iSup_typein_limit {o : Ordinal.{u}} (ho : ∀ a, a < o → succ a < o) :
    iSup (typein ((· < ·) : o.ToType → o.ToType → Prop)) = o := by
  replace ho : IsSuccPrelimit o := by rwa [isSuccPrelimit_iff_succ_lt]
  rw [iSup, PrincipalSeg.range_eq]
  simpa [Iio_def] using ho.sSup_Iio

@[deprecated csSup_Iic (since := "2026-03-27")]
/-
**Ordinal.iSup_typein_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_typein_succ {o : Ordinal} : iSup (typein ((· < ·) : (succ o).ToType -
> (succ o).ToType -> Prop)) = o
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csSup_Iic`：csSup_Iic : sSup (Iic a) = a
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `PrincipalSeg.range_eq`：range_eq (f : r ≺i s) : Set.range f = {b | s b f.
top}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_typein_succ {o : Ordinal} :
    iSup (typein ((· < ·) : (succ o).ToType → (succ o).ToType → Prop)) = o := by
  rw [← csSup_Iic (a := o), iSup, PrincipalSeg.range_eq]
  congr
  simp

end lsub

section blsub

/-- The least strict upper bound of a family of ordinals indexed by the set of ordinals less than
some `o : Ordinal.{u}`. -/
@[deprecated "write `⨆ i : Iio o, f i + 1` instead." (since := "2026-03-23")]
/-
**Ordinal.blsub** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：blsub (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v}) : Ordinal.{m
ax u v}
参数：o : Ordinal.{u}；f : forall a < o, Ordinal.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The least strict upper bound of a family of ordinals indexed by the set of ordin
als less than
some `o : Ordinal.{u}`.
-/
def blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  bsup.{_, v} o fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_eq_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_blsub (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v}) : (b
sup.{_, v} o fun a ha => succ (f a ha)) = blsub.{_, v} o f
参数：o : Ordinal.{u}；f : forall a < o, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bsup_eq_blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) :
    (bsup.{_, v} o fun a ha => succ (f a ha)) = blsub.{_, v} o f :=
  rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.lsub_eq_blsub'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_eq_blsub' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho
 : type r = o) (f : forall a < o, Ordinal) : lsub (familyOfBFamily' r ho f) = bl
sub o f
参数：r : ι -> ι -> Prop；ho : type r = o；f : forall a < o, Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup'_eq_bsup`：∀ {o : Ordinal.{u_3}} {ι : Type u_3} (r : ι → ι →
 Prop) [inst : IsWellOrder ι r] (ho : Ordinal.type r = o)   (f : (a : Ordinal.{u
_3}) → a < …
-/
theorem lsub_eq_blsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, Ordinal) : lsub (familyOfBFamily' r ho f) = blsub o f :=
  iSup'_eq_bsup r ho fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.lsub_eq_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_eq_lsub {ι ι' : Type u} (r : ι -> ι -> Prop) (r' : ι' -> ι' -> Prop) 
[IsWellOrder ι r] [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o) 
(f : forall a < o, Ordinal.{max u v}) : lsub.{_, v} (familyOfBFamily' r ho f) = 
lsub.{_, v} (familyOfBFamily' r' ho' f)
参数：r : ι -> ι -> Prop；r' : ι' -> ι' -> Prop；ho : type r = o；ho' : type r' = o；f 
: forall a < o, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lsub_eq_blsub'`：lsub_eq_blsub' {ι : Type u} (r : ι -> ι -> Prop)
 [IsWellOrder ι r] {o} (ho : type r = o) (f : forall a < o, Ordinal) : lsub (fam
ilyOfBFamily…
-/
theorem lsub_eq_lsub {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily' r ho f) = lsub.{_, v} (familyOfBFamily' r' ho' f) := by
  rw [lsub_eq_blsub', lsub_eq_blsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.lsub_eq_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_eq_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) : ls
ub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lsub_eq_blsub'`：lsub_eq_blsub' {ι : Type u} (r : ι -> ι -> Prop)
 [IsWellOrder ι r] {o} (ho : type r = o) (f : forall a < o, Ordinal) : lsub (fam
ilyOfBFamily…
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem lsub_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f :=
  lsub_eq_blsub' _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_eq_lsub'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_eq_lsub' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι 
-> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r f) = lsub.{_, v} f
参数：r : ι -> ι -> Prop；f : ι -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup'_eq_iSup`：∀ {ι : Type u_3} (r : ι → ι → Prop) [inst : IsWel
lOrder ι r] (f : ι → Ordinal.{max u_3 u_4}),   (Ordinal.type r).bsup (Ordinal.bf
amilyOfFami…
-/
theorem blsub_eq_lsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r]
    (f : ι → Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r f) = lsub.{_, v} f :=
  bsup'_eq_iSup r (succ ∘ f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_eq_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_eq_blsub {ι : Type u} (r r' : ι -> ι -> Prop) [IsWellOrder ι r] [IsW
ellOrder ι r'] (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r
 f) = blsub.{_, v} _ (bfamilyOfFamily' r' f)
参数：r r' : ι -> ι -> Prop；f : ι -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.blsub_eq_lsub'`：blsub_eq_lsub' {ι : Type u} (r : ι -> ι -> Prop)
 [IsWellOrder ι r] (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamil
y' r f) = ls…
-/
theorem blsub_eq_blsub {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily' r f) = blsub.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [blsub_eq_lsub', blsub_eq_lsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_eq_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_eq_lsub {ι : Type u} (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (
bfamilyOfFamily f) = lsub.{_, v} f
参数：f : ι -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.blsub_eq_lsub'`：blsub_eq_lsub' {ι : Type u} (r : ι -> ι -> Prop)
 [IsWellOrder ι r] (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamil
y' r f) = ls…
-/
theorem blsub_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily f) = lsub.{_, v} f :=
  blsub_eq_lsub' _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_congr** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_congr {o₁ o₂ : Ordinal.{u}} (f : forall a < o₁, Ordinal.{max u v}) (
ho : o₁ = o₂) : blsub.{_, v} o₁ f = blsub.{_, v} o₂ fun a h => f a (h.trans_eq h
o.symm)
参数：f : forall a < o₁, Ordinal.{max u v}；ho : o₁ = o₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem blsub_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    blsub.{_, v} o₁ f = blsub.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_le_iff {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}} {a} :
 blsub.{_, v} o f <= a ↔ forall i h, f i h < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Ordinal.bsup_le_iff`：bsup_le_iff {o f a} : bsup.{u, v} o f <= a ↔ forall
 i h, f i h <= a
-/
theorem blsub_le_iff {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} {a} :
    blsub.{_, v} o f ≤ a ↔ ∀ i h, f i h < a := by
  convert! bsup_le_iff.{_, v} (f := fun a ha => succ (f a ha)) (a := a) using 2
  simp_rw [succ_le_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a} : (forall i h, f i 
h < a) -> blsub o f <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.blsub_le_iff`：blsub_le_iff {o : Ordinal.{u}} {f : forall a < o, 
Ordinal.{max u v}} {a} : blsub.{_, v} o f <= a ↔ forall i h, f i h < a
-/
theorem blsub_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} : (∀ i h, f i h < a) → blsub o f ≤ a :=
  blsub_le_iff.2

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.lt_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h < blsub o f
参数：f : forall a < o, Ordinal；i h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.blsub_le_iff`：blsub_le_iff {o : Ordinal.{u}} {f : forall a < o, 
Ordinal.{max u v}} {a} : blsub.{_, v} o f <= a ↔ forall i h, f i h < a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lt_blsub {o} (f : ∀ a < o, Ordinal) (i h) : f i h < blsub o f :=
  blsub_le_iff.1 le_rfl _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.lt_blsub_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_blsub_iff {o : Ordinal.{u}} {f : forall b < o, Ordinal.{max u v}} {a} :
 a < blsub.{_, v} o f ↔ exists i hi, a <= f i hi
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.blsub_le_iff`：blsub_le_iff {o : Ordinal.{u}} {f : forall a < o, 
Ordinal.{max u v}} {a} : blsub.{_, v} o f <= a ↔ forall i h, f i h < a
-/
theorem lt_blsub_iff {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v}} {a} :
    a < blsub.{_, v} o f ↔ ∃ i hi, a ≤ f i hi := by
  simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff.{_, v} _ f a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_le_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_le_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) : bs
up.{_, v} o f <= blsub.{_, v} o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_le`：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
 (forall i h, f i h <= a) -> bsup.{u, v} o f <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.lt_blsub`：lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h
 < blsub o f
-/
theorem bsup_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f ≤ blsub.{_, v} o f :=
  bsup_le fun i h => (lt_blsub f i h).le

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_le_bsup_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_le_bsup_succ {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
 : blsub.{_, v} o f <= succ (bsup.{_, v} o f)
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.blsub_le`：blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a}
 : (forall i h, f i h < a) -> blsub o f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
-/
theorem blsub_le_bsup_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    blsub.{_, v} o f ≤ succ (bsup.{_, v} o f) :=
  blsub_le fun i h => lt_succ_iff.2 (le_bsup f i h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_eq_blsub_or_succ_bsup_eq_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
`。
形式化陈述：bsup_eq_blsub_or_succ_bsup_eq_blsub {o : Ordinal.{u}} (f : forall a < o, O
rdinal.{max u v}) : bsup.{_, v} o f = blsub.{_, v} o f ∨ succ (bsup.{_, v} o f) 
= blsub.{_, v} o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_eq_bsup`：iSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordi
nal) : iSup (familyOfBFamily o f) = bsup o f
· 使用定理 `Ordinal.lsub_eq_blsub`：lsub_eq_blsub {o : Ordinal.{u}} (f : forall a < o
, Ordinal.{max u v}) : lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f
· 使用定理 `Ordinal.iSup_eq_lsub_or_succ_iSup_eq_lsub`：iSup_eq_lsub_or_succ_iSup_eq_
lsub {ι} (f : ι -> Ordinal) : iSup f = lsub f ∨ succ (iSup f) = lsub f
-/
theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ∨ succ (bsup.{_, v} o f) = blsub.{_, v} o f := by
  rw [← iSup_eq_bsup, ← lsub_eq_blsub]
  exact iSup_eq_lsub_or_succ_iSup_eq_lsub _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_succ_le_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_succ_le_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
 : succ (bsup.{_, v} o f) <= blsub.{_, v} o f ↔ exists i hi, f i hi = bsup.{_, v
} o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.bsup_le_blsub`：bsup_le_blsub {o : Ordinal.{u}} (f : forall a < o
, Ordinal.{max u v}) : bsup.{_, v} o f <= blsub.{_, v} o f
· 使用定理 `Ordinal.blsub_le`：blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a}
 : (forall i h, f i h < a) -> blsub o f <= a
· 使用定理 `Ordinal.lt_bsup_of_ne_bsup`：lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : fo
rall a < o, Ordinal.{max u v}} : (forall i h, f i h != bsup.{_, v} o f) ↔ forall
 i h, f i h < bs…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_blsub`：lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h
 < blsub o f
-/
theorem bsup_succ_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) ≤ blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact
      ne_of_lt (succ_le_iff.1 h)
        (le_antisymm (bsup_le_blsub f) (blsub_le (lt_bsup_of_ne_bsup.1 hf)))
  rintro ⟨_, _, hf⟩
  rw [succ_le_iff, ← hf]
  exact lt_blsub _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_succ_eq_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_succ_eq_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
 : succ (bsup.{_, v} o f) = blsub.{_, v} o f ↔ exists i hi, f i hi = bsup.{_, v}
 o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Ordinal.blsub_le_bsup_succ`：blsub_le_bsup_succ {o : Ordinal.{u}} (f : fo
rall a < o, Ordinal.{max u v}) : blsub.{_, v} o f <= succ (bsup.{_, v} o f)
· 使用定理 `Ordinal.bsup_succ_le_blsub`：bsup_succ_le_blsub {o : Ordinal.{u}} (f : fo
rall a < o, Ordinal.{max u v}) : succ (bsup.{_, v} o f) <= blsub.{_, v} o f ↔ ex
ists i hi, f i h…
-/
theorem bsup_succ_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) = blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f :=
  (blsub_le_bsup_succ f).ge_iff_eq'.symm.trans (bsup_succ_le_blsub f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_eq_blsub_iff_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_blsub_iff_succ {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u
 v}) : bsup.{_, v} o f = blsub.{_, v} o f ↔ forall a < blsub.{_, v} o f, succ a 
< blsub.{_, v} o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_eq_bsup`：iSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordi
nal) : iSup (familyOfBFamily o f) = bsup o f
· 使用定理 `Ordinal.lsub_eq_blsub`：lsub_eq_blsub {o : Ordinal.{u}} (f : forall a < o
, Ordinal.{max u v}) : lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f
· 使用定理 `Ordinal.iSup_eq_lsub_iff`：iSup_eq_lsub_iff {ι} (f : ι -> Ordinal) : iSup
 f = lsub f ↔ forall a < lsub f, succ a < lsub f
-/
theorem bsup_eq_blsub_iff_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ a < blsub.{_, v} o f, succ a < blsub.{_, v} o f := by
  rw [← iSup_eq_bsup, ← lsub_eq_blsub]
  apply iSup_eq_lsub_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_eq_blsub_iff_lt_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_blsub_iff_lt_bsup {o : Ordinal.{u}} (f : forall a < o, Ordinal.{ma
x u v}) : bsup.{_, v} o f = blsub.{_, v} o f ↔ forall i hi, f i hi < bsup.{_, v}
 o f
参数：f : forall a < o, Ordinal.{max u v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_blsub`：lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h
 < blsub o f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.bsup_le_blsub`：bsup_le_blsub {o : Ordinal.{u}} (f : forall a < o
, Ordinal.{max u v}) : bsup.{_, v} o f <= blsub.{_, v} o f
· 使用定理 `Ordinal.blsub_le`：blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a}
 : (forall i h, f i h < a) -> blsub o f <= a
-/
theorem bsup_eq_blsub_iff_lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ i hi, f i hi < bsup.{_, v} o f :=
  ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_eq_blsub_of_lt_succ_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_eq_blsub_of_lt_succ_limit {o : Ordinal.{u}} (ho : IsSuccLimit o) {f :
 forall a < o, Ordinal.{max u v}} (hf : forall a ha, f a ha < f (succ a) (ho.suc
c_lt ha)) : bsup.{_, v} o f = blsub.{_, v} o f
参数：ho : IsSuccLimit o；hf : forall a ha, f a ha < f (succ a) (ho.succ_lt ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.bsup_eq_blsub_iff_lt_bsup`：bsup_eq_blsub_iff_lt_bsup {o : Ordina
l.{u}} (f : forall a < o, Ordinal.{max u v}) : bsup.{_, v} o f = blsub.{_, v} o 
f ↔ forall i hi, f i hi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
-/
theorem bsup_eq_blsub_of_lt_succ_limit {o : Ordinal.{u}} (ho : IsSuccLimit o)
    {f : ∀ a < o, Ordinal.{max u v}} (hf : ∀ a ha, f a ha < f (succ a) (ho.succ_lt ha)) :
    bsup.{_, v} o f = blsub.{_, v} o f := by
  rw [bsup_eq_blsub_iff_lt_bsup]
  exact fun i hi => (hf i hi).trans_le (le_bsup f _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_succ_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_succ_of_mono {o : Ordinal.{u}} {f : forall a < succ o, Ordinal.{max 
u v}} (hf : forall {i j} (hi hj), i <= j -> f i hi <= f j hj) : blsub.{_, v} _ f
 = succ (f o (lt_succ o))
参数：hf : forall {i j} (hi hj), i <= j -> f i hi <= f j hj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_succ_of_mono`：bsup_succ_of_mono {o : Ordinal} {f : forall a
 < succ o, Ordinal} (hf : forall {i j} (hi hj), i <= j -> f i hi <= f j hj) : bs
up _ f = f o (l…
· 使用定理 `Order.succ_le_succ`：succ_le_succ (h : a <= b) : succ a <= succ b
-/
theorem blsub_succ_of_mono {o : Ordinal.{u}} {f : ∀ a < succ o, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : blsub.{_, v} _ f = succ (f o (lt_succ o)) :=
  bsup_succ_of_mono fun {_ _} hi hj h => succ_le_succ (hf hi hj h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_eq_zero_iff {o} {f : forall a < o, Ordinal} : blsub o f = 0 ↔ o = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lsub_eq_blsub`：lsub_eq_blsub {o : Ordinal.{u}} (f : forall a < o
, Ordinal.{max u v}) : lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f
· 使用定理 `Ordinal.lsub_eq_zero_iff`：lsub_eq_zero_iff {ι} (f : ι -> Ordinal) : lsub
.{_, v} f = 0 ↔ IsEmpty ι
· 使用定理 `Ordinal.isEmpty_toType_iff`：isEmpty_toType_iff {o : Ordinal} : IsEmpty o
.ToType ↔ o = 0
-/
theorem blsub_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : blsub o f = 0 ↔ o = 0 := by
  rw [← lsub_eq_blsub, lsub_eq_zero_iff]
  exact isEmpty_toType_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_zero (f : forall a < (0 : Ordinal), Ordinal) : blsub 0 f = 0
参数：f : forall a < (0 : Ordinal), Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.blsub_eq_zero_iff`：blsub_eq_zero_iff {o} {f : forall a < o, Ordi
nal} : blsub o f = 0 ↔ o = 0
-/
theorem blsub_zero (f : ∀ a < (0 : Ordinal), Ordinal) : blsub 0 f = 0 := by rw [blsub_eq_zero_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_pos {o : Ordinal} (ho : 0 < o) (f : forall a < o, Ordinal) : 0 < bls
ub o f
参数：ho : 0 < o；f : forall a < o, Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.lt_blsub`：lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h
 < blsub o f
-/
theorem blsub_pos {o : Ordinal} (ho : 0 < o) (f : ∀ a < o, Ordinal) : 0 < blsub o f :=
  (lt_blsub f 0 ho).pos

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_type {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : forall
 a < type r, Ordinal.{max u v}) : blsub.{_, v} (type r) f = lsub.{_, v} fun a =>
 f (typein r a) (typein_lt_type _ _)
参数：r : α -> α -> Prop；f : forall a < type r, Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.blsub_le_iff`：blsub_le_iff {o : Ordinal.{u}} {f : forall a < o, 
Ordinal.{max u v}} {a} : blsub.{_, v} o f <= a ↔ forall i h, f i h < a
· 使用定理 `Ordinal.lsub_le_iff`：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= 
a ↔ forall i, f i < a
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem blsub_type {α : Type u} (r : α → α → Prop) [IsWellOrder α r]
    (f : ∀ a < type r, Ordinal.{max u v}) :
    blsub.{_, v} (type r) f = lsub.{_, v} fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff fun o => by
    rw [blsub_le_iff, lsub_le_iff]
    exact ⟨fun H b => H _ _, fun H i h => by simpa only [typein_enum] using H (enum r ⟨i, h⟩)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_const** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_const {o : Ordinal} (ho : o != 0) (a : Ordinal) : (blsub.{u, v} o fu
n _ _ => a) = succ a
参数：ho : o != 0；a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_const`：bsup_const {o : Ordinal.{u}} (ho : o != 0) (a : Ordi
nal.{max u v}) : (bsup.{_, v} o fun _ _ => a) = a
-/
theorem blsub_const {o : Ordinal} (ho : o ≠ 0) (a : Ordinal) :
    (blsub.{u, v} o fun _ _ => a) = succ a :=
  bsup_const.{u, v} ho (succ a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_one (f : forall a < (1 : Ordinal), Ordinal) : blsub 1 f = succ (f 0 
zero_lt_one)
参数：f : forall a < (1 : Ordinal), Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_one`：bsup_one (f : forall a < (1 : Ordinal), Ordinal) : bsu
p 1 f = f 0 zero_lt_one
-/
theorem blsub_one (f : ∀ a < (1 : Ordinal), Ordinal) : blsub 1 f = succ (f 0 zero_lt_one) :=
  bsup_one _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_id** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_id : forall o, (blsub.{u, u} o fun x _ => x) = o
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lsub_typein`：lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α
-/
theorem blsub_id : ∀ o, (blsub.{u, u} o fun x _ => x) = o :=
  lsub_typein

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-23")]
/-
**Ordinal.bsup_id_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_id_limit {o : Ordinal} : (forall a < o, succ a < o) -> (bsup.{u, u} o
 fun x _ => x) = o
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_typein_limit`：iSup_typein_limit {o : Ordinal.{u}} (ho : for
all a, a < o -> succ a < o) : iSup (typein ((· < ·) : o.ToType -> o.ToType -> Pr
op)) = o
-/
theorem bsup_id_limit {o : Ordinal} : (∀ a < o, succ a < o) → (bsup.{u, u} o fun x _ => x) = o :=
  iSup_typein_limit

@[deprecated csSup_Iic (since := "2026-03-23")]
/-
**Ordinal.bsup_id_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_id_add_one (o) : (bsup.{u, u} (o + 1) fun x _ => x) = o
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_typein_succ`：iSup_typein_succ {o : Ordinal} : iSup (typein 
((· < ·) : (succ o).ToType -> (succ o).ToType -> Prop)) = o
-/
theorem bsup_id_add_one (o) : (bsup.{u, u} (o + 1) fun x _ => x) = o :=
  iSup_typein_succ

@[deprecated csSup_Iic (since := "2026-03-23")]
/-
**Ordinal.bsup_id_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_id_succ (o) : (bsup.{u, u} (succ o) fun x _ => x) = o
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_typein_succ`：iSup_typein_succ {o : Ordinal} : iSup (typein 
((· < ·) : (succ o).ToType -> (succ o).ToType -> Prop)) = o
-/
theorem bsup_id_succ (o) : (bsup.{u, u} (succ o) fun x _ => x) = o :=
  iSup_typein_succ

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_le_of_brange_subset** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_le_of_brange_subset {o o'} {f : forall a < o, Ordinal} {g : forall a
 < o', Ordinal} (h : brange o f subseteq brange o' g) : blsub.{u, max v w} o f <
= blsub.{v, max u w} o' g
参数：h : brange o f subseteq brange o' g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_le_of_brange_subset`：bsup_le_of_brange_subset {o o'} {f : f
orall a < o, Ordinal} {g : forall a < o', Ordinal} (h : brange o f subseteq bran
ge o' g) : bsup.{u, ma…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem blsub_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : blsub.{u, max v w} o f ≤ blsub.{v, max u w} o' g :=
  bsup_le_of_brange_subset.{u, v, w} fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc'] at hb'
    exact ⟨c, hc, hb'⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_eq_of_brange_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_eq_of_brange_eq {o o'} {f : forall a < o, Ordinal} {g : forall a < o
', Ordinal} (h : { o | exists i hi, f i hi = o } = { o | exists i hi, g i hi = o
 }) : blsub.{u, max v w} o f = blsub.{v, max u w} o' g
参数：h : { o | exists i hi, f i hi = o } = { o | exists i hi, g i hi = o }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.blsub_le_of_brange_subset`：blsub_le_of_brange_subset {o o'} {f :
 forall a < o, Ordinal} {g : forall a < o', Ordinal} (h : brange o f subseteq br
ange o' g) : blsub.{u, …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem blsub_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : { o | ∃ i hi, f i hi = o } = { o | ∃ i hi, g i hi = o }) :
    blsub.{u, max v w} o f = blsub.{v, max u w} o' g :=
  (blsub_le_of_brange_subset.{u, v, w} h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.bsup_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_comp {o o' : Ordinal.{max u v}} {f : forall a < o, Ordinal.{max u v w
}} (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj) {g : forall a < o',
 Ordinal.{max u v}} (hg : blsub.{_, u} o' g = o) : (bsup.{_, w} o' fun a ha => f
 (g a ha) (by rw [← hg]; apply lt_blsub)) = bsup.{_, w} o f
参数：hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj；hg : blsub.{_, u} o' 
g = o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.bsup_le`：bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
 (forall i h, f i h <= a) -> bsup.{u, v} o f <= a
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_blsub_iff`：lt_blsub_iff {o : Ordinal.{u}} {f : forall b < o, 
Ordinal.{max u v}} {a} : a < blsub.{_, v} o f ↔ exists i hi, a <= f i hi
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem bsup_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (bsup.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = bsup.{_, w} o f := by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/-
**Ordinal.blsub_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_comp {o o' : Ordinal.{max u v}} {f : forall a < o, Ordinal.{max u v 
w}} (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj) {g : forall a < o'
, Ordinal.{max u v}} (hg : blsub.{_, u} o' g = o) : (blsub.{_, w} o' fun a ha =>
 f (g a ha) (by rw [← hg]; apply lt_blsub)) = blsub.{_, w} o f
参数：hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj；hg : blsub.{_, u} o' 
g = o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_comp`：bsup_comp {o o' : Ordinal.{max u v}} {f : forall a < 
o, Ordinal.{max u v w}} (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj
) {g : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_le_succ_iff`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 
: SuccOrder α] {a b : α} [NoMaxOrder α],   Order.succ a ≤ Order.succ b ↔ a ≤ b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem blsub_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (blsub.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = blsub.{_, w} o f :=
  @bsup_comp.{u, v, w} o _ (fun a ha => succ (f a ha))
    (fun {_ _} _ _ h => succ_le_succ_iff.2 (hf _ _ h)) g hg

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]
/-
**Ordinal.IsNormal.bsup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsNormal`。
形式化陈述：∀ {f : Ordinal.{u} → Ordinal.{max u v}},   Order.IsNormal f → ∀ {o : Ordin
al.{u}}, Order.IsSuccLimit o → (o.bsup fun x x_1 => f x) = f o
参数：o.bsup fun x x_1 => f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsNormal.bsup`：∀ {f : Ordinal.{max u_3 u_4} → Ordinal.{max u_4 u
_5}},   Order.IsNormal f →     ∀ {o : Ordinal.{u_4}} (g : (a : Ordinal.{u_4}) → 
a < o → Ord…
· 使用定理 `Order.IsSuccLimit.ne_bot`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → a ≠ ⊥
· 使用定理 `Ordinal.bsup_id_limit`：bsup_id_limit {o : Ordinal} : (forall a < o, succ
 a < o) -> (bsup.{u, u} o fun x _ => x) = o
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
-/
theorem IsNormal.bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsSuccLimit o) : (Ordinal.bsup.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup.{u, u, v} H (fun x _ => x) h.ne_bot, bsup_id_limit fun _ ↦ h.succ_lt]

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]
/-
**Ordinal.IsNormal.blsub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsNormal`。
形式化陈述：∀ {f : Ordinal.{u} → Ordinal.{max u v}},   Order.IsNormal f → ∀ {o : Ordin
al.{u}}, Order.IsSuccLimit o → (o.blsub fun x x_1 => f x) = f o
参数：o.blsub fun x x_1 => f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsNormal.bsup_eq`：∀ {f : Ordinal.{u} → Ordinal.{max u v}},   Ord
er.IsNormal f → ∀ {o : Ordinal.{u}}, Order.IsSuccLimit o → (o.bsup fun x x_1 => 
f x) = f o
· 使用定理 `Ordinal.bsup_eq_blsub_of_lt_succ_limit`：bsup_eq_blsub_of_lt_succ_limit {
o : Ordinal.{u}} (ho : IsSuccLimit o) {f : forall a < o, Ordinal.{max u v}} (hf 
: forall a ha, f a ha < f (s…
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem IsNormal.blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsSuccLimit o) : (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup_eq.{u, v} H h, bsup_eq_blsub_of_lt_succ_limit h]
  exact fun a _ => H.strictMono (lt_succ a)

@[deprecated isNormal_iff (since := "2026-03-23")]
/-
**Ordinal.isNormal_iff_lt_succ_and_bsup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_iff_lt_succ_and_bsup_eq {f : Ordinal.{u} -> Ordinal.{max u v}} : 
IsNormal f ↔ (forall a, f a < f (succ a)) ∧ forall o, IsSuccLimit o -> (bsup.{_,
 v} o fun x _ => f x) = f o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.IsNormal.bsup_eq`：∀ {f : Ordinal.{u} → Ordinal.{max u v}},   Ord
er.IsNormal f → ∀ {o : Ordinal.{u}}, Order.IsSuccLimit o → (o.bsup fun x x_1 => 
f x) = f o
· 使用定理 `Order.IsNormal.of_succ_lt`：of_succ_lt (hs : forall a, f a < f (succ a)) 
(hl : forall {a}, IsSuccLimit a -> IsLUB (f '' Iio a) (f a)) : IsNormal f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ordinal.le_bsup`：le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <
= bsup o f
-/
theorem isNormal_iff_lt_succ_and_bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧
      ∀ o, IsSuccLimit o → (bsup.{_, v} o fun x _ => f x) = f o :=
  ⟨fun h => ⟨fun a ↦ h.strictMono (lt_succ a), @IsNormal.bsup_eq f h⟩, fun ⟨h₁, h₂⟩ =>
    .of_succ_lt h₁ fun ho ↦ by
      rw [← h₂ _ ho]
      simpa [IsLUB, upperBounds, lowerBounds, IsLeast, bsup_le_iff] using le_bsup _⟩

@[deprecated isNormal_iff (since := "2026-03-23")]
/-
**Ordinal.isNormal_iff_lt_succ_and_blsub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_iff_lt_succ_and_blsub_eq {f : Ordinal.{u} -> Ordinal.{max u v}} :
 IsNormal f ↔ (forall a, f a < f (succ a)) ∧ forall o, IsSuccLimit o -> (blsub.{
_, v} o fun x _ => f x) = f o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isNormal_iff_lt_succ_and_bsup_eq`：isNormal_iff_lt_succ_and_bsup_
eq {f : Ordinal.{u} -> Ordinal.{max u v}} : IsNormal f ↔ (forall a, f a < f (suc
c a)) ∧ forall o, IsSuccLimit …
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.bsup_eq_blsub_of_lt_succ_limit`：bsup_eq_blsub_of_lt_succ_limit {
o : Ordinal.{u}} (ho : IsSuccLimit o) {f : forall a < o, Ordinal.{max u v}} (hf 
: forall a ha, f a ha < f (s…
-/
theorem isNormal_iff_lt_succ_and_blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧
      ∀ o, IsSuccLimit o → (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [isNormal_iff_lt_succ_and_bsup_eq.{u, v}, and_congr_right_iff]
  intro h
  constructor <;> intro H o ho <;> have := H o ho <;>
    rwa [← bsup_eq_blsub_of_lt_succ_limit ho fun a _ => h a] at *

end blsub

end Ordinal

/-! ### Results about injectivity and surjectivity -/


/-
**not_surjective_of_ordinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_surjective_of_ordinal {α : Type*} [Small.{u} α] (f : α -> Ordinal.{u})
 : ¬ Surjective f
参数：f : α -> Ordinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_iSup_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], a < ⨆ i, f i ↔ ∃ i, a < f i
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}

--- 原说明 ---
### Results about injectivity and surjectivity
-/
theorem not_surjective_of_ordinal {α : Type*} [Small.{u} α] (f : α → Ordinal.{u}) :
    ¬ Surjective f := by
  intro h
  obtain ⟨a, ha⟩ := h (⨆ i, succ (f i))
  apply ha.not_lt
  rw [Ordinal.lt_iSup_iff]
  exact ⟨a, Order.lt_succ _⟩
/-
**not_injective_of_ordinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_injective_of_ordinal {α : Type*} [Small.{u} α] (f : Ordinal.{u} -> α) 
: ¬ Injective f
参数：f : Ordinal.{u} -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_surjective_of_ordinal`：not_surjective_of_ordinal {α : Type*} [Small.
{u} α] (f : α -> Ordinal.{u}) : ¬ Surjective f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
-/
theorem not_injective_of_ordinal {α : Type*} [Small.{u} α] (f : Ordinal.{u} → α) :
    ¬ Injective f := fun h ↦ not_surjective_of_ordinal _ (invFun_surjective h)

/-- The type of ordinals in universe `u` is not `Small.{u}`. This is the type-theoretic analog of
the Burali-Forti paradox. -/
/-
**not_small_ordinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_small_ordinal : ¬Small.{u} Ordinal.{max u v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_injective_of_ordinal`：not_injective_of_ordinal {α : Type*} [Small.{u
} α] (f : Ordinal.{u} -> α) : ¬ Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lift_inj`：lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v}
 b ↔ a = b

--- 原说明 ---
The type of ordinals in universe `u` is not `Small.{u}`. This is the type-theore
tic analog of
the Burali-Forti paradox.
-/
theorem not_small_ordinal : ¬Small.{u} Ordinal.{max u v} := fun h =>
  @not_injective_of_ordinal _ h _ fun _a _b => Ordinal.lift_inj.{v, u}.1
/-
**Ordinal.uncountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ordinal.uncountable : Uncountable Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Uncountable.of_not_small`：Uncountable.of_not_small {α : Type v} (h : ¬ S
mall.{w} α) : Uncountable α
· 使用定理 `not_small_ordinal`：not_small_ordinal : ¬Small.{u} Ordinal.{max u v}
-/
instance Ordinal.uncountable : Uncountable Ordinal.{u} :=
  Uncountable.of_not_small not_small_ordinal.{u}
/-
**Ordinal.not_bddAbove_compl_of_small** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ordinal.not_bddAbove_compl_of_small (s : Set Ordinal.{u}) [hs : Small.{u} 
s] : ¬BddAbove sᶜ
参数：s : Set Ordinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.bddAbove_iff_small`：bddAbove_iff_small {s : Set Ordinal.{u}} : B
ddAbove s ↔ Small.{u} s
· 使用定理 `not_small_ordinal`：not_small_ordinal : ¬Small.{u} Ordinal.{max u v}
· 使用定理 `small_univ_iff`：small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
-/
theorem Ordinal.not_bddAbove_compl_of_small (s : Set Ordinal.{u}) [hs : Small.{u} s] :
    ¬BddAbove sᶜ := by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self, small_univ_iff] at this
  exact not_small_ordinal this

namespace Ordinal

/-! ### Casting naturals into ordinals, compatibility with operations -/

@[simp]
/-
**Ordinal.iSup_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_natCast : iSup Nat.cast = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.omega0_le`：omega0_le {o : Ordinal} : ω <= o ↔ forall n : Nat, ↑n
 <= o
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
### Casting naturals into ordinals, compatibility with operations
-/
theorem iSup_natCast : iSup Nat.cast = ω :=
  (Ordinal.iSup_le fun n => (natCast_lt_omega0 n).le).antisymm <| omega0_le.2 <| Ordinal.le_iSup _
/-
**Ordinal.apply_omega0_of_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_omega0_of_isNormal {f : Ordinal.{u} -> Ordinal.{v}} (hf : IsNormal f
) : ⨆ n : Nat, f n = f ω
参数：hf : IsNormal f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_natCast`：iSup_natCast : iSup Nat.cast = ω
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem apply_omega0_of_isNormal {f : Ordinal.{u} → Ordinal.{v}} (hf : IsNormal f) :
    ⨆ n : ℕ, f n = f ω := by
  rw [← iSup_natCast, hf.map_iSup bddAbove_of_small]

@[simp]
/-
**Ordinal.add_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_iSup (o : Ordinal.{u}) {ι} [Small.{u} ι] [Nonempty ι] (f : ι -> Ordina
l) : o + ⨆ i, f i = ⨆ i, o + f i
参数：o : Ordinal.{u}；f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
-/
theorem add_iSup (o : Ordinal.{u}) {ι} [Small.{u} ι] [Nonempty ι] (f : ι → Ordinal) :
    o + ⨆ i, f i = ⨆ i, o + f i :=
  (isNormal_add_right o).map_iSup bddAbove_of_small

@[simp]
/-
**Ordinal.add_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_sSup (o : Ordinal.{u}) {s : Set Ordinal} [Small.{u} s] (hs : s.Nonempt
y) : o + sSup s = sSup ((o + ·) '' s)
参数：o : Ordinal.{u}；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.map_sSup`：map_sSup (hf : IsNormal f) {s : Set α} (hs : s.
Nonempty) (hs' : BddAbove s) : f (sSup s) = sSup (f '' s)
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
-/
theorem add_sSup (o : Ordinal.{u}) {s : Set Ordinal} [Small.{u} s] (hs : s.Nonempty) :
    o + sSup s = sSup ((o + ·) '' s) :=
  (isNormal_add_right o).map_sSup hs bddAbove_of_small

@[simp]
/-
**Ordinal.mul_sSup** 是 Mathlib 中的一个引理，位于命名空间 `Ordinal`。
形式化陈述：mul_sSup (o : Ordinal) (s : Set Ordinal) : o * sSup s = sSup ((o * ·) '' s
)
参数：o : Ordinal；s : Set Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `csSup_singleton`：csSup_singleton (a : α) : sSup {a} = a
· 使用定理 `Order.IsNormal.map_sSup`：map_sSup (hf : IsNormal f) {s : Set α} (hs : s.
Nonempty) (hs' : BddAbove s) : f (sSup s) = sSup (f '' s)
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.le_mul_right`：le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 <
 b) : a <= b * a
-/
lemma mul_sSup (o : Ordinal) (s : Set Ordinal) : o * sSup s = sSup ((o * ·) '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases eq_zero_or_pos o with (rfl | ho)
  · simp [hs.image_const]
  by_cases bdd : BddAbove s
  · exact (isNormal_mul_right ho).map_sSup hs bdd
  · rw [csSup_of_not_bddAbove bdd, csSup_empty, csSup_of_not_bddAbove]
    · simp
    exact fun ⟨u, hu⟩ ↦ bdd ⟨u, fun x hx ↦ (x.le_mul_right ho).trans (hu ⟨x, hx, rfl⟩)⟩

@[simp]
/-
**Ordinal.mul_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Ordinal`。
形式化陈述：mul_iSup (o : Ordinal) {ι} (f : ι -> Ordinal) : o * ⨆ i, f i = ⨆ i, o * f 
i
参数：o : Ordinal；f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用引理 `Ordinal.mul_sSup`：mul_sSup (o : Ordinal) (s : Set Ordinal) : o * sSup s 
= sSup ((o * ·) '' s)
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
-/
lemma mul_iSup (o : Ordinal) {ι} (f : ι → Ordinal) : o * ⨆ i, f i = ⨆ i, o * f i := by
  rw [← sSup_range, mul_sSup, ← Set.range_comp', sSup_range]

@[simp]
/-
**Ordinal.iSup_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_add_natCast (o : Ordinal) : ⨆ n : Nat, o + n = o + ω
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_natCast`：iSup_natCast : iSup Nat.cast = ω
· 使用定理 `Ordinal.add_iSup`：add_iSup (o : Ordinal.{u}) {ι} [Small.{u} ι] [Nonempty
 ι] (f : ι -> Ordinal) : o + ⨆ i, f i = ⨆ i, o + f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem iSup_add_natCast (o : Ordinal) : ⨆ n : ℕ, o + n = o + ω := by
  rw [← iSup_natCast, Ordinal.add_iSup]

@[simp]
/-
**Ordinal.iSup_mul_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_mul_natCast (o : Ordinal) : ⨆ n : Nat, o * n = o * ω
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_natCast`：iSup_natCast : iSup Nat.cast = ω
· 使用引理 `Ordinal.mul_iSup`：mul_iSup (o : Ordinal) {ι} (f : ι -> Ordinal) : o * ⨆ 
i, f i = ⨆ i, o * f i
-/
theorem iSup_mul_natCast (o : Ordinal) : ⨆ n : ℕ, o * n = o * ω := by
  rw [← iSup_natCast, Ordinal.mul_iSup]

end Ordinal

