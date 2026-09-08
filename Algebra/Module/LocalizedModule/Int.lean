/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!

# Integer elements of a localized module

This is a mirror of the corresponding notion for localizations of rings.

## Main definitions

* `IsLocalizedModule.IsInteger` is a predicate stating that `m : M'` is in the image of `M`

## Implementation details

After `IsLocalizedModule` and `IsLocalization` are unified, the two `IsInteger` predicates
can be unified.

-/

@[expose] public section


variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

open Function

namespace IsLocalizedModule

/-- Given `x : M'`, `M'` a localization of `M` via `f`, `IsInteger f x` iff `x` is in the image of
the localization map `f`. -/
/-
**IsLocalizedModule.IsInteger** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：IsInteger (x : M') : Prop
参数：x : M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `x : M'`, `M'` a localization of `M` via `f`, `IsInteger f x` iff `x` is i
n the image of
the localization map `f`.
-/
def IsInteger (x : M') : Prop :=
  x ∈ LinearMap.range f
/-
**IsLocalizedModule.isInteger_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：isInteger_zero : IsInteger f (0 : M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
lemma isInteger_zero : IsInteger f (0 : M') :=
  Submodule.zero_mem _
/-
**IsLocalizedModule.isInteger_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：isInteger_add {x y : M'} (hx : IsInteger f x) (hy : IsInteger f y) : IsInt
eger f (x + y)
参数：hx : IsInteger f x；hy : IsInteger f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
theorem isInteger_add {x y : M'} (hx : IsInteger f x) (hy : IsInteger f y) : IsInteger f (x + y) :=
  Submodule.add_mem _ hx hy
/-
**IsLocalizedModule.isInteger_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：isInteger_smul {a : R} {x : M'} (hx : IsInteger f x) : IsInteger f (a • x)
参数：hx : IsInteger f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMapClass.map_smul`：∀ {R : outParam (Type u_14)} {M : outParam (Typ
e u_15)} {M₂ : outParam (Type u_16)} [inst : Semiring R]   [inst_1 : AddCommMono
id M] [inst_2…
-/
theorem isInteger_smul {a : R} {x : M'} (hx : IsInteger f x) : IsInteger f (a • x) := by
  rcases hx with ⟨x', hx⟩
  use a • x'
  rw [← hx, LinearMapClass.map_smul]

variable (S)
variable [IsLocalizedModule S f]

/-- Each element `x : M'` has an `S`-multiple which is an integer. -/
/-
**IsLocalizedModule.exists_integer_multiple** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
edModule`。
形式化陈述：exists_integer_multiple (x : M') : exists a : S, IsInteger f (a.val • x)
参数：x : M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Each element `x : M'` has an `S`-multiple which is an integer.
-/
theorem exists_integer_multiple (x : M') : ∃ a : S, IsInteger f (a.val • x) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/-- We can clear the denominators of a `Finset`-indexed family of fractions. -/
/-
**IsLocalizedModule.exist_integer_multiples** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
edModule`。
形式化陈述：exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι -> M') : exists 
b : S, forall i in s, IsInteger f (b.val • g i)
参数：s : Finset ι；g : ι -> M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.coe_finsetProd`：coe_finsetProd {ι M} [CommMonoid M] (S : Submo
noid M) (f : ι -> S) (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
We can clear the denominators of a `Finset`-indexed family of fractions.
-/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι → M') :
    ∃ b : S, ∀ i ∈ s, IsInteger f (b.val • g i) := by
  classical
  choose sec hsec using (fun i ↦ IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i ∈ s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finsetProd]
    rw [← hsec, ← mul_smul, Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finsetProd, mul_comm]
    rw [← Finset.prod_insert (f := fun i ↦ ((sec i).snd).val) (s.notMem_erase i),
      Finset.insert_erase hi]

/-- We can clear the denominators of a finite indexed family of fractions. -/
/-
**IsLocalizedModule.exist_integer_multiples_of_finite** 是 Mathlib 中的一个定理，位于命名空间 
`IsLocalizedModule`。
形式化陈述：exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι -> M') : e
xists b : S, forall i, IsInteger f ((b : R) • g i)
参数：g : ι -> M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsLocalizedModule.exist_integer_multiples`：exist_integer_multiples {ι : 
Type*} (s : Finset ι) (g : ι -> M') : exists b : S, forall i in s, IsInteger f (
b.val • g i)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
We can clear the denominators of a finite indexed family of fractions.
-/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι → M') :
    ∃ b : S, ∀ i, IsInteger f ((b : R) • g i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/-- We can clear the denominators of a finite set of fractions. -/
/-
**IsLocalizedModule.exist_integer_multiples_of_finset** 是 Mathlib 中的一个定理，位于命名空间 
`IsLocalizedModule`。
形式化陈述：exist_integer_multiples_of_finset (s : Finset M') : exists b : S, forall a
 in s, IsInteger f ((b : R) • a)
参数：s : Finset M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.exist_integer_multiples`：exist_integer_multiples {ι : 
Type*} (s : Finset ι) (g : ι -> M') : exists b : S, forall i in s, IsInteger f (
b.val • g i)

--- 原说明 ---
We can clear the denominators of a finite set of fractions.
-/
theorem exist_integer_multiples_of_finset (s : Finset M') :
    ∃ b : S, ∀ a ∈ s, IsInteger f ((b : R) • a) :=
  exist_integer_multiples S f s id

/-- A choice of a common multiple of the denominators of a `Finset`-indexed family of fractions. -/
/-
**IsLocalizedModule.commonDenom** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：commonDenom {ι : Type*} (s : Finset ι) (g : ι -> M') : S
参数：s : Finset ι；g : ι -> M'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.exist_integer_multiples`：exist_integer_multiples {ι : 
Type*} (s : Finset ι) (g : ι -> M') : exists b : S, forall i in s, IsInteger f (
b.val • g i)

--- 原说明 ---
A choice of a common multiple of the denominators of a `Finset`-indexed family o
f fractions.
-/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (g : ι → M') : S :=
  (exist_integer_multiples S f s g).choose

/-- The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions. -/
/-
**IsLocalizedModule.integerMultiple** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule
`。
形式化陈述：integerMultiple {ι : Type*} (s : Finset ι) (g : ι -> M') (i : s) : M
参数：s : Finset ι；g : ι -> M'；i : s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.exist_integer_multiples`：exist_integer_multiples {ι : 
Type*} (s : Finset ι) (g : ι -> M') : exists b : S, forall i in s, IsInteger f (
b.val • g i)

--- 原说明 ---
The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions.
-/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) : M :=
  ((exist_integer_multiples S f s g).choose_spec i i.prop).choose

@[simp]
/-
**IsLocalizedModule.map_integerMultiple** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedMo
dule`。
形式化陈述：map_integerMultiple {ι : Type*} (s : Finset ι) (g : ι -> M') (i : s) : f (
integerMultiple S f s g i) = commonDenom S f s g • g i
参数：s : Finset ι；g : ι -> M'；i : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsLocalizedModule.exist_integer_multiples`：exist_integer_multiples {ι : 
Type*} (s : Finset ι) (g : ι -> M') : exists b : S, forall i in s, IsInteger f (
b.val • g i)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) :
    f (integerMultiple S f s g i) = commonDenom S f s g • g i :=
  ((exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
/-
**IsLocalizedModule.commonDenomOfFinset** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedMo
dule`。
形式化陈述：commonDenomOfFinset (s : Finset M') : S
参数：s : Finset M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of a common multiple of the denominators of a finite set of fractions.
-/
noncomputable def commonDenomOfFinset (s : Finset M') : S :=
  commonDenom S f s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
/-
**IsLocalizedModule.finsetIntegerMultiple** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalized
Module`。
形式化陈述：finsetIntegerMultiple [DecidableEq M] (s : Finset M') : Finset M
参数：s : Finset M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of numerators after clearing the denominators of a finite set of frac
tions.
-/
noncomputable def finsetIntegerMultiple [DecidableEq M] (s : Finset M') : Finset M :=
  s.attach.image fun t => integerMultiple S f s id t

open scoped Pointwise
/-
**IsLocalizedModule.finsetIntegerMultiple_image** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alizedModule`。
形式化陈述：finsetIntegerMultiple_image [DecidableEq M] (s : Finset M') : f '' finsetI
ntegerMultiple S f s = commonDenomOfFinset S f s • (s : Set M')
参数：s : Finset M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsLocalizedModule.map_integerMultiple`：map_integerMultiple {ι : Type*} (
s : Finset ι) (g : ι -> M') (i : s) : f (integerMultiple S f s g i) = commonDeno
m S f s g • g i
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
-/
theorem finsetIntegerMultiple_image [DecidableEq M] (s : Finset M') :
    f '' finsetIntegerMultiple S f s = commonDenomOfFinset S f s • (s : Set M') := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple S f s id _⟩

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalizedModule.smul_mem_finsetIntegerMultiple_span** 是 Mathlib 中的一个定理，位于命名空
间 `IsLocalizedModule`。
形式化陈述：smul_mem_finsetIntegerMultiple_span [DecidableEq M] (x : M) (s : Finset M'
) (hx : f x in Submodule.span R s) : exists (m : S), m • x in Submodule.span R (
IsLocalizedModule.finsetIntegerMultiple S f s)
参数：x : M；s : Finset M'；hx : f x in Submodule.span R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.finsetIntegerMultiple_image`：finsetIntegerMultiple_ima
ge [DecidableEq M] (s : Finset M') : f '' finsetIntegerMultiple S f s = commonDe
nomOfFinset S f s • (s : Set M')
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Submodule.span_smul`：span_smul (a : α) (s : Set M) : span R (a • s) = a 
• span R s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalizedModule.eq_iff_exists`：IsLocalizedModule.eq_iff_exists [IsLoca
lizedModule S f] {x₁ x₂} : f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem smul_mem_finsetIntegerMultiple_span [DecidableEq M] (x : M) (s : Finset M')
    (hx : f x ∈ Submodule.span R s) :
    ∃ (m : S), m • x ∈ Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s) := by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : y • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  rw [hx₁, ← f.map_smul, ← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert!
    (Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem a hx'
      using 1
  convert! ha.symm using 1
  simp only [Submonoid.smul_def, ← smul_smul]

end IsLocalizedModule

