/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.DFinsupp.Defs

/-!
# Extensionality principles for `DFinsupp`

## Main results

* `DFinsupp.addHom_ext`, `DFinsupp.addHom_ext'`: if two additive homomorphisms from `Π₀ i, β i`
  are equal on each `single a b`, then they are equal.
-/

public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section DecidableEq
variable [DecidableEq ι]

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
/-
**DFinsupp.add_closure_iUnion_range_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：add_closure_iUnion_range_single : AddSubmonoid.closure (⋃ i : ι, Set.range
 (single i : β i -> Π₀ i, β i)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `DFinsupp.induction`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq 
ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   {p : (Π₀ (i : ι), β i) → Prop} (f :
 Π₀ (i :…
· 使用定理 `AddSubmonoid.zero_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : Add
Submonoid M), 0 ∈ S
· 使用定理 `AddSubmonoid.add_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : AddS
ubmonoid M) {x y : M}, x ∈ S → y ∈ S → x + y ∈ S
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem add_closure_iUnion_range_single :
    AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i → Π₀ i, β i)) = ⊤ :=
  top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
/-
**DFinsupp.addHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) ->+ γ⦄ (H : fo
rall (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.eq_of_eqOn_denseM`：∀ {M : Type u_1} {N : Type u_2} [inst : 
AddZeroClass M] [inst_1 : AddZeroClass N] {s : Set M},   AddSubmonoid.closure s 
= ⊤ → ∀ {f g : M →+ …
· 使用定理 `DFinsupp.add_closure_iUnion_range_single`：add_closure_iUnion_range_singl
e : AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i -> Π₀ i, β i)) = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, t
hen
they are equal.
-/
theorem addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g := by
  refine AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => ?_
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
/-
**DFinsupp.addHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) ->+ γ⦄ (H : f
orall x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.addHom_ext`：addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀
 i, β i) ->+ γ⦄ (H : forall (i : ι) (y : β i), f (single i y) = g (single i y)) 
: f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, t
hen
they are equal.

See note [partially-applied ext lemmas].
-/
theorem addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)

end AddMonoid

end DecidableEq

end DFinsupp

