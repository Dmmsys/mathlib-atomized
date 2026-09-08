/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Defining a monoid given by generators and relations

Given relations `rels` on the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `rels`.

## Main definitions

* `PresentedMonoid rels`: the quotient of the free monoid on a type `α` by the closure of one-step
  reductions (arising from a binary relation on free monoid elements `rels`).
* `PresentedMonoid.of`: The canonical map from `α` to a presented monoid with generators `α`.
* `PresentedMonoid.lift f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given
  a function `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

@[expose] public section

variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quotient of a congruence structure over rels. -/
@[to_additive /-- Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an AddCon structure over
rels -/]
/-
**PresentedMonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PresentedMonoid (rels : FreeMonoid α -> FreeMonoid α -> Prop)
参数：rels : FreeMonoid α -> FreeMonoid α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def PresentedMonoid (rels : FreeMonoid α → FreeMonoid α → Prop) := (conGen rels).Quotient

namespace PresentedMonoid

open Set Submonoid

@[to_additive]
/-
**PresentedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `PresentedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {rels : FreeMonoid α → FreeMonoid α → Prop} : Monoid (PresentedMonoid rels) :=
  inferInstanceAs <| Monoid (conGen rels).Quotient

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive /-- The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels` -/]
/-
**PresentedMonoid.mk** 是 Mathlib 中的一个定义，位于命名空间 `PresentedMonoid`。
形式化陈述：mk (rels : FreeMonoid α -> FreeMonoid α -> Prop) : FreeMonoid α ->* Presen
tedMonoid rels where toFun
参数：rels : FreeMonoid α -> FreeMonoid α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk (rels : FreeMonoid α → FreeMonoid α → Prop) : FreeMonoid α →* PresentedMonoid rels where
  toFun := Quotient.mk (conGen rels).toSetoid
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive
/-- `of` is the canonical map from `α` to a presented additive monoid with generators `x : α`. The
term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α`. -/]
/-
**PresentedMonoid.of** 是 Mathlib 中的一个定义，位于命名空间 `PresentedMonoid`。
形式化陈述：of (rels : FreeMonoid α -> FreeMonoid α -> Prop) (x : α) : PresentedMonoid
 rels
参数：rels : FreeMonoid α -> FreeMonoid α -> Prop；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def of (rels : FreeMonoid α → FreeMonoid α → Prop) (x : α) : PresentedMonoid rels :=
  mk rels (.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

local notation "P₁" => PresentedMonoid rels₁
local notation "P₂" => PresentedMonoid rels₂
local notation "P₃" => PresentedMonoid rels₃

@[to_additive (attr := elab_as_elim), induction_eliminator]
/-
**PresentedMonoid.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：∀ {α₁ : Type u_2} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop} {δ : Pres
entedMonoid rels₁ → Prop}   (q : PresentedMonoid rels₁), (∀ (a : FreeMonoid α₁),
 δ ((PresentedMonoid.mk rels₁) a)) → δ q
参数：q : PresentedMonoid rels₁；∀ (a : FreeMonoid α₁), δ ((PresentedMonoid.mk rels₁
) a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
protected theorem inductionOn {δ : P₁ → Prop} (q : P₁) (h : ∀ a, δ (mk rels₁ a)) : δ q :=
  Quotient.ind h q

@[to_additive (attr := elab_as_elim)]
/-
**PresentedMonoid.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：∀ {α₁ : Type u_2} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop} {δ : Pres
entedMonoid rels₁ → Prop}   (q : PresentedMonoid rels₁), (∀ (a : FreeMonoid α₁),
 δ ((PresentedMonoid.mk rels₁) a)) → δ q
参数：q : PresentedMonoid rels₁；∀ (a : FreeMonoid α₁), δ ((PresentedMonoid.mk rels₁
) a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
protected theorem inductionOn₂ {δ : P₁ → P₂ → Prop} (q₁ : P₁) (q₂ : P₂)
    (h : ∀ a b, δ (mk rels₁ a) (mk rels₂ b)) : δ q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

@[to_additive (attr := elab_as_elim)]
/-
**PresentedMonoid.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：∀ {α₁ : Type u_2} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop} {δ : Pres
entedMonoid rels₁ → Prop}   (q : PresentedMonoid rels₁), (∀ (a : FreeMonoid α₁),
 δ ((PresentedMonoid.mk rels₁) a)) → δ q
参数：q : PresentedMonoid rels₁；∀ (a : FreeMonoid α₁), δ ((PresentedMonoid.mk rels₁
) a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
protected theorem inductionOn₃ {δ : P₁ → P₂ → P₃ → Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : ∀ a b c, δ (mk rels₁ a) (mk rels₂ b) (mk rels₃ c)) :
    δ q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

end inductionOn

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

/-
**PresentedMonoid.mk_eq_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `PresentedMonoid`。
形式化陈述：mk_eq_mk_iff : mk rels x = mk rels y ↔ conGen rels x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
lemma mk_eq_mk_iff : mk rels x = mk rels y ↔ conGen rels x y := Quotient.eq
/-
**PresentedMonoid.mk_eq_mk_of_rel** 是 Mathlib 中的一个引理，位于命名空间 `PresentedMonoid`。
形式化陈述：mk_eq_mk_of_rel (h : rels x y) : mk rels x = mk rels y
参数：h : rels x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PresentedMonoid.mk_eq_mk_iff`：mk_eq_mk_iff : mk rels x = mk rels y ↔ con
Gen rels x y
-/
lemma mk_eq_mk_of_rel (h : rels x y) : mk rels x = mk rels y := mk_eq_mk_iff.2 (.of _ _ h)

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) /-- The generators of a presented additive monoid generate the
presented additive monoid. That is, the additive submonoid closure of the set of generators equals
`⊤`. -/]
/-
**PresentedMonoid.closure_range_of** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：closure_range_of (rels : FreeMonoid α -> FreeMonoid α -> Prop) : Submonoid
.closure (Set.range (of rels)) = ⊤
参数：rels : FreeMonoid α -> FreeMonoid α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.eq_top_iff'`：eq_top_iff' : S = ⊤ ↔ forall x : M, x in S
· 使用定理 `PresentedMonoid.inductionOn`：∀ {α₁ : Type u_2} {rels₁ : FreeMonoid α₁ → 
FreeMonoid α₁ → Prop} {δ : PresentedMonoid rels₁ → Prop}   (q : PresentedMonoid 
rels₁), (∀ (a : F…
· 使用定理 `FreeMonoid.inductionOn`：∀ {α : Type u_1} {motive : FreeMonoid α → Prop} 
(z : FreeMonoid α),   motive 1 →     (∀ (x : α), motive (FreeMonoid.of x)) → (∀ 
(x y : FreeM…
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
-/
theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
    Submonoid.closure (Set.range (of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
  | of x => exact subset_closure <| by simp [range, of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

@[to_additive]
/-
**PresentedMonoid.surjective_mk** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：surjective_mk {rels : FreeMonoid α -> FreeMonoid α -> Prop} : Function.Sur
jective (mk rels)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresentedMonoid.inductionOn`：∀ {α₁ : Type u_2} {rels₁ : FreeMonoid α₁ → 
FreeMonoid α₁ → Prop} {δ : PresentedMonoid rels₁ → Prop}   (q : PresentedMonoid 
rels₁), (∀ (a : F…
-/
theorem surjective_mk {rels : FreeMonoid α → FreeMonoid α → Prop} :
    Function.Surjective (mk rels) := fun x ↦ PresentedMonoid.inductionOn x fun a ↦ .intro a rfl

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b → FreeMonoid.lift f a = FreeMonoid.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive /-- The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M` -/]
/-
**PresentedMonoid.lift** 是 Mathlib 中的一个定义，位于命名空间 `PresentedMonoid`。
形式化陈述：lift : PresentedMonoid rels ->* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lift : PresentedMonoid rels →* M :=
  Con.lift _ (FreeMonoid.lift f) (Con.conGen_le.2 h)

@[to_additive]
/-
**PresentedMonoid.toMonoid.unique** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid.toM
onoid`。
形式化陈述：∀ {α : Type u_3} {M : Type u_4} [inst : Monoid M] (f : α → M) {rels : Free
Monoid α → FreeMonoid α → Prop}   (h : ∀ (a b : FreeMonoid α), rels a b → (FreeM
onoid.lift f) a = (FreeMonoid.lift f) b)   (g : (conGen rels).Quotient →* M), (∀
 (a : α), g (PresentedMonoid.of rels a) = f a) → g = PresentedMonoid.lift f h
参数：f : α → M；h : ∀ (a b : FreeMonoid α), rels a b → (FreeMonoid.lift f) a = (Fre
eMonoid.lift f) b；g : (conGen rels).Quotient →* M；∀ (a : α), g (PresentedMonoid.
of rels a) = f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.lift_unique`：lift_unique (H : c <= ker f) (g : c.Quotient ->* P) (Hg
 : g.comp c.mk' = f) : g = c.lift f H
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Con.conGen_le`：conGen_le {r : M -> M -> Prop} {c : Con M} : conGen r <= 
c ↔ r <= ⇑c
· 使用定理 `FreeMonoid.hom_eq`：hom_eq ⦃f g : FreeMonoid α ->* M⦄ (h : forall x, f (o
f x) = g (of x)) : f = g
-/
theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = lift f h :=
  Con.lift_unique (Con.conGen_le.2 h) g (FreeMonoid.hom_eq hg)

@[to_additive (attr := simp)]
/-
**PresentedMonoid.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：lift_of {x : α} : lift f h (of rels x) = f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_of {x : α} : lift f h (of rels x) = f x := rfl

end ToMonoid

@[to_additive (attr := ext)]
/-
**PresentedMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 `PresentedMonoid`。
形式化陈述：ext {M : Type*} [Monoid M] (rels : FreeMonoid α -> FreeMonoid α -> Prop) {
φ ψ : PresentedMonoid rels ->* M} (hx : forall (x : α), φ (.of rels x) = ψ (.of 
rels x)) : φ = ψ
参数：rels : FreeMonoid α -> FreeMonoid α -> Prop；hx : forall (x : α), φ (.of rels 
x) = ψ (.of rels x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.eq_of_eqOn_denseM`：eq_of_eqOn_denseM {s : Set M} (hs : closure
 s = ⊤) {f g : M ->* N} (h : s.EqOn f g) : f = g
· 使用定理 `PresentedMonoid.closure_range_of`：closure_range_of (rels : FreeMonoid α 
-> FreeMonoid α -> Prop) : Submonoid.closure (Set.range (of rels)) = ⊤
-/
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  apply MonoidHom.eq_of_eqOn_denseM (closure_range_of _)
  grind [Set.eqOn_range]

end PresentedMonoid

