/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Locality conditions on object properties

In this file we define locality conditions on object properties in a category. Let `K` be a
precoverage in a category `C` and `P` be an object property that is closed under isomorphisms.

We say that

- `P` is local if for every `X : C`, `P` holds for `X` if and only if it holds for `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `X`.

## Implementation details

The covers appearing in the definitions have index type in the morphism universe of `C`.
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- An object property is local if it holds for `X` if and only if it holds for all `Uᵢ` where
`{Uᵢ}` is a `K`-cover of `X`. -/
/-
**CategoryTheory.ObjectProperty.IsLocal** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.ObjectProperty C → CategoryTheory.Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object property is local if it holds for `X` if and only if it holds for all 
`Uᵢ` where
`{Uᵢ}` is a `K`-cover of `X`.
-/
class IsLocal (P : ObjectProperty C) (K : Precoverage C) extends IsClosedUnderIsomorphisms P where
  component {X : C} {R : Presieve X} (hR : R ∈ K X) {Y : C} (f : Y ⟶ X) (hf : R f) : P X → P Y
  of_presieve {X : C} {R : Presieve X} (hR : R ∈ K X) (H : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → P Y) : P X

export IsLocal (of_presieve)

variable {P : ObjectProperty C} {K L : Precoverage C}
/-
**CategoryTheory.ObjectProperty.iff_of_presieve** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：iff_of_presieve [P.IsLocal K] {X : C} {R : Presieve X} (hR : R in K X) : P
 X ↔ forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f -> P Y
参数：hR : R in K X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.component`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K : C
ategoryTheory.Precoverage C} [self : …
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.of_presieve`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K :
 CategoryTheory.Precoverage C} [self : …
-/
lemma iff_of_presieve [P.IsLocal K] {X : C} {R : Presieve X} (hR : R ∈ K X) :
    P X ↔ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → P Y :=
  ⟨fun h _ _ hf ↦ IsLocal.component hR _ hf h, fun h ↦ of_presieve hR h⟩

namespace IsLocal

/-
**CategoryTheory.ObjectProperty.IsLocal.mk_of_zeroHypercover** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty.IsLocal`。
形式化陈述：mk_of_zeroHypercover [P.IsClosedUnderIsomorphisms] (H : forall ⦃X : C⦄ (𝒰 
: Precoverage.ZeroHypercover.{max u v} K X), P X ↔ forall i, P (𝒰.X i)) : P.IsLo
cal K where component {X R} hR Y f hf hX
参数：H : forall ⦃X : C⦄ (𝒰 : Precoverage.ZeroHypercover.{max u v} K X), P X ↔ fora
ll i, P (𝒰.X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover`：mem_iff_exists
_zeroHypercover {X : C} {R : Presieve X} : R in J X ↔ exists (𝒰 : ZeroHypercover
.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma mk_of_zeroHypercover [P.IsClosedUnderIsomorphisms]
    (H : ∀ ⦃X : C⦄ (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
      P X ↔ ∀ i, P (𝒰.X i)) :
    P.IsLocal K where
  component {X R} hR Y f hf hX := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰] at hX
    obtain ⟨i⟩ := hf
    exact hX i
  of_presieve {X R} hR h := by
    rw [CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨𝒰, rfl⟩ := hR
    rw [H 𝒰]
    intro i
    exact h ⟨i⟩
/-
**CategoryTheory.ObjectProperty.IsLocal.of_le** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty.IsLocal`。
形式化陈述：of_le [IsLocal P L] (hle : K <= L) : IsLocal P K where component hR _ f hf
 hX
参数：hle : K <= L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.toIsClosedUnderIsomorphisms`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPr
operty C}   (K : CategoryTheory.Precoverage C) [self : …
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.component`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K : C
ategoryTheory.Precoverage C} [self : …
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.of_presieve`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K :
 CategoryTheory.Precoverage C} [self : …
-/
lemma of_le [IsLocal P L] (hle : K ≤ L) : IsLocal P K where
  component hR _ f hf hX := component (hle _ hR) f hf hX
  of_presieve hR H := of_presieve (hle _ hR) H
/-
**CategoryTheory.ObjectProperty.IsLocal.top** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.ObjectProperty.IsLocal`。
形式化陈述：top : IsLocal (⊤ : ObjectProperty C) K where component
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsClosedUnderIsomorphisms
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance top : IsLocal (⊤ : ObjectProperty C) K where
  component := by simp
  of_presieve := by simp
/-
**CategoryTheory.ObjectProperty.IsLocal.inf** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.ObjectProperty.IsLocal`。
形式化陈述：inf (P Q : ObjectProperty C) [IsLocal P K] [IsLocal Q K] : IsLocal (P ⊓ Q)
 K where component hR _ _ hf h
参数：P Q : ObjectProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsMin`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P Q : CategoryTheory.ObjectPro
perty C)   [P.IsClosedUnderIsomorphisms] [Q.IsClosed…
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.toIsClosedUnderIsomorphisms`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPr
operty C}   (K : CategoryTheory.Precoverage C) [self : …
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.component`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K : C
ategoryTheory.Precoverage C} [self : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.of_presieve`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K :
 CategoryTheory.Precoverage C} [self : …
-/
instance inf (P Q : ObjectProperty C) [IsLocal P K] [IsLocal Q K] :
    IsLocal (P ⊓ Q) K where
  component hR _ _ hf h := ⟨component hR _ hf h.1, component hR _ hf h.2⟩
  of_presieve hR h := ⟨of_presieve hR fun _ _ hf ↦ (h hf).1, of_presieve hR fun _ _ hf ↦ (h hf).2⟩

end IsLocal

/-
**CategoryTheory.ObjectProperty.of_zeroHypercover** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) (h : fora
ll i, P (𝒰.X i)) : P X
参数：𝒰 : K.ZeroHypercover X；h : forall i, P (𝒰.X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.of_presieve`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K :
 CategoryTheory.Precoverage C} [self : …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) (h : ∀ i, P (𝒰.X i)) : P X :=
  P.of_presieve 𝒰.mem₀ fun _ f ⟨i⟩ ↦ h i
/-
**CategoryTheory.ObjectProperty.iff_of_zeroHypercover** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：iff_of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) : P X
 ↔ forall i, P (𝒰.X i)
参数：𝒰 : K.ZeroHypercover X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsLocal.component`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {K : C
ategoryTheory.Precoverage C} [self : …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用引理 `CategoryTheory.ObjectProperty.of_zeroHypercover`：of_zeroHypercover [P.Is
Local K] {X : C} (𝒰 : K.ZeroHypercover X) (h : forall i, P (𝒰.X i)) : P X
-/
lemma iff_of_zeroHypercover [P.IsLocal K] {X : C} (𝒰 : K.ZeroHypercover X) :
    P X ↔ ∀ i, P (𝒰.X i) :=
  ⟨fun h i ↦ IsLocal.component 𝒰.mem₀ _ ⟨i⟩ h, fun h ↦ of_zeroHypercover 𝒰 h⟩

end CategoryTheory.ObjectProperty

