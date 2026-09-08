/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Topology.Category.Profinite.Product
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Preliminaries for Nöbeling's theorem

This file constructs basic objects and results concerning them that are needed in the proof of
Nöbeling's theorem, which is in `Mathlib/Topology/Category/Profinite/Nobeling/Induction.lean`.
See the section docstrings for more information.

## Proof idea

We follow the proof of theorem 5.4 in [scholze2019condensed], in which the idea is to embed `S` in
a product of `I` copies of `Bool` for some sufficiently large `I`, and then to choose a
well-ordering on `I` and use ordinal induction over that well-order. Here we can let `I` be
the set of clopen subsets of `S` since `S` is totally separated.

The above means it suffices to prove the following statement: For a closed subset `C` of `I → Bool`,
the `ℤ`-module `LocallyConstant C ℤ` is free.

For `i : I`, let `e C i : LocallyConstant C ℤ` denote the map `fun f ↦ (if f.val i then 1 else 0)`.

The basis will consist of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be written
as linear combinations of lexicographically smaller products. We call this set `GoodProducts C`.

What is proved by ordinal induction (in
`Mathlib/Topology/Category/Profinite/Nobeling/ZeroLimit.lean` and
`Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean`) is that this set is linearly
independent. The fact that it spans is proved directly in
`Mathlib/Topology/Category/Profinite/Nobeling/Span.lean`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

open CategoryTheory ContinuousMap Limits Opposite Submodule

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool))

section Projections
/-!
## Projection maps

The purpose of this section is twofold.

Firstly, in the proof that the set `GoodProducts C` spans the whole module `LocallyConstant C ℤ`,
we need to project `C` down to finite discrete subsets and write `C` as a cofiltered limit of those.

Secondly, in the inductive argument, we need to project `C` down to "smaller" sets satisfying the
inductive hypothesis.

In this section we define the relevant projection maps and prove some compatibility results.

### Main definitions

* Let `J : I → Prop`. Then `Proj J : (I → Bool) → (I → Bool)` is the projection mapping everything
  that satisfies `J i` to itself, and everything else to `false`.

* The image of `C` under `Proj J` is denoted `π C J` and the corresponding map `C → π C J` is called
  `ProjRestrict`. If `J` implies `K` we have a map `ProjRestricts : π C K → π C J`.

* `spanCone_isLimit` establishes that when `C` is compact, it can be written as a limit of its
  images under the maps `Proj (· ∈ s)` where `s : Finset I`.
-/

variable (J K L : I → Prop) [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

/--
The projection mapping everything that satisfies `J i` to itself, and everything else to `false`
-/
/-
**Profinite.NobelingProof.Proj** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProo
f`。
形式化陈述：Proj : (I -> Bool) -> (I -> Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection mapping everything that satisfies `J i` to itself, and everything
 else to `false`
-/
def Proj : (I → Bool) → (I → Bool) :=
  fun c i ↦ if J i then c i else false

@[simp]
/-
**Profinite.NobelingProof.continuous_proj** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.N
obelingProof`。
形式化陈述：continuous_proj : Continuous (Proj J : (I -> Bool) -> (I -> Bool))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem continuous_proj :
    Continuous (Proj J : (I → Bool) → (I → Bool)) := by
  dsimp +unfoldPartialApp [Proj]
  apply continuous_pi
  intro i
  split <;> fun_prop

/-- The image of `Proj π J` -/
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `Proj π J`
-/
def π : Set (I → Bool) := (Proj J) '' C

/-- The restriction of `Proj π J` to a subset, mapping to its image. -/
@[simps!]
/-
**Profinite.NobelingProof.ProjRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：ProjRestrict : C -> π C J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of `Proj π J` to a subset, mapping to its image.
-/
def ProjRestrict : C → π C J :=
  Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]
/-
**Profinite.NobelingProof.continuous_projRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Pro
finite.NobelingProof`。
形式化陈述：continuous_projRestrict : Continuous (ProjRestrict C J)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.restrict`：Continuous.restrict {f : X -> Y} {s : Set X} {t : S
et Y} (h1 : MapsTo f s t) (h2 : Continuous f) : Continuous (h1.restrict f s t)
· 使用定理 `Profinite.NobelingProof.continuous_proj`：continuous_proj : Continuous (P
roj J : (I -> Bool) -> (I -> Bool))
-/
theorem continuous_projRestrict : Continuous (ProjRestrict C J) :=
  Continuous.restrict _ (continuous_proj _)
/-
**Profinite.NobelingProof.proj_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：proj_eq_self {x : I -> Bool} (h : forall i, x i != false -> J i) : Proj J 
x = x
参数：h : forall i, x i != false -> J i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem proj_eq_self {x : I → Bool} (h : ∀ i, x i ≠ false → J i) : Proj J x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff]
  contrapose!
  simpa only [ne_comm] using h i
/-
**Profinite.NobelingProof.proj_prop_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof`。
形式化陈述：proj_prop_eq_self (hh : forall i x, x in C -> x i != false -> J i) : π C J
 = C
参数：hh : forall i x, x in C -> x i != false -> J i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.proj_eq_self`：proj_eq_self {x : I -> Bool} (h : 
forall i, x i != false -> J i) : Proj J x = x
-/
theorem proj_prop_eq_self (hh : ∀ i x, x ∈ C → x i ≠ false → J i) : π C J = C := by
  ext x
  refine ⟨fun ⟨y, hy, h⟩ ↦ ?_, fun h ↦ ⟨x, h, ?_⟩⟩
  · rwa [← h, proj_eq_self]; exact (hh · y hy)
  · rw [proj_eq_self]; exact (hh · x h)
/-
**Profinite.NobelingProof.proj_comp_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Profini
te.NobelingProof`。
形式化陈述：proj_comp_of_subset (h : forall i, J i -> K i) : (Proj J ∘ Proj K) = (Proj
 J : (I -> Bool) -> (I -> Bool))
参数：h : forall i, J i -> K i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.if_false_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p th
en t else false) = (decide p && t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem proj_comp_of_subset (h : ∀ i, J i → K i) : (Proj J ∘ Proj K) =
    (Proj J : (I → Bool) → (I → Bool)) := by
  ext x i; dsimp [Proj]; simp_all
/-
**Profinite.NobelingProof.proj_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof`。
形式化陈述：proj_eq_of_subset (h : forall i, J i -> K i) : π (π C K) J = π C J
参数：h : forall i, J i -> K i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.proj_comp_of_subset`：proj_comp_of_subset (h : fo
rall i, J i -> K i) : (Proj J ∘ Proj K) = (Proj J : (I -> Bool) -> (I -> Bool))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem proj_eq_of_subset (h : ∀ i, J i → K i) : π (π C K) J = π C J := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := h
    refine ⟨z, hz, (?_ : _ = (Proj J ∘ Proj K) z)⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy, rfl⟩ := h
    dsimp [π]
    rw [← Set.image_comp]
    refine ⟨y, hy, ?_⟩
    rw [proj_comp_of_subset J K h]

variable {J K L}

/-- A variant of `ProjRestrict` with domain of the form `π C K` -/
@[simps!]
/-
**Profinite.NobelingProof.ProjRestricts** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nob
elingProof`。
形式化陈述：ProjRestricts (h : forall i, J i -> K i) : π C K -> π C J
参数：h : forall i, J i -> K i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.proj_eq_of_subset`：proj_eq_of_subset (h : forall
 i, J i -> K i) : π (π C K) J = π C J

--- 原说明 ---
A variant of `ProjRestrict` with domain of the form `π C K`
-/
def ProjRestricts (h : ∀ i, J i → K i) : π C K → π C J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (π C K) J

@[simp]
/-
**Profinite.NobelingProof.continuous_projRestricts** 是 Mathlib 中的一个定理，位于命名空间 `Pr
ofinite.NobelingProof`。
形式化陈述：continuous_projRestricts (h : forall i, J i -> K i) : Continuous (ProjRest
ricts C h)
参数：h : forall i, J i -> K i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Profinite.NobelingProof.proj_eq_of_subset`：proj_eq_of_subset (h : forall
 i, J i -> K i) : π (π C K) J = π C J
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Profinite.NobelingProof.continuous_projRestrict`：continuous_projRestrict
 : Continuous (ProjRestrict C J)
-/
theorem continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)
/-
**Profinite.NobelingProof.surjective_projRestricts** 是 Mathlib 中的一个定理，位于命名空间 `Pr
ofinite.NobelingProof`。
形式化陈述：surjective_projRestricts (h : forall i, J i -> K i) : Function.Surjective 
(ProjRestricts C h)
参数：h : forall i, J i -> K i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Profinite.NobelingProof.proj_eq_of_subset`：proj_eq_of_subset (h : forall
 i, J i -> K i) : π (π C K) J = π C J
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Set.surjective_mapsTo_image_restrict`：surjective_mapsTo_image_restrict (
f : α -> β) (s : Set α) : Surjective ((mapsTo_image f s).restrict f s (f '' s))
-/
theorem surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  (Homeomorph.surjective _).comp (Set.surjective_mapsTo_image_restrict _ _)

set_option backward.isDefEq.respectTransparency.types false in
variable (J) in
/-
**Profinite.NobelingProof.projRestricts_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Profini
te.NobelingProof`。
形式化陈述：projRestricts_eq_id : ProjRestricts C (fun i (h : J i) => h) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.ProjRestricts_coe`：∀ {I : Type u} (C : Set (I → 
Bool)) {J K : I → Prop} [inst : (i : I) → Decidable (J i)]   [inst_1 : (i : I) →
 Decidable (K i)] (h : ∀ (i : I…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projRestricts_eq_id : ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext ⟨x, y, hy, rfl⟩ i
  simp +contextual only [π, Proj, ProjRestricts_coe, id_eq, if_true]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.projRestricts_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof`。
形式化陈述：projRestricts_eq_comp (hJK : forall i, J i -> K i) (hKL : forall i, K i ->
 L i) : ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i => hK
L i ∘ hJK i)
参数：hJK : forall i, J i -> K i；hKL : forall i, K i -> L i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Profinite.NobelingProof.ProjRestricts_coe`：∀ {I : Type u} (C : Set (I → 
Bool)) {J K : I → Prop} [inst : (i : I) → Decidable (J i)]   [inst_1 : (i : I) →
 Decidable (K i)] (h : ∀ (i : I…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.if_false_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p th
en t else false) = (decide p && t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe]
  simp_all

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.projRestricts_comp_projRestrict** 是 Mathlib 中的一个定理，位于命
名空间 `Profinite.NobelingProof`。
形式化陈述：projRestricts_comp_projRestrict (h : forall i, J i -> K i) : ProjRestricts
 C h ∘ ProjRestrict C K = ProjRestrict C J
参数：h : forall i, J i -> K i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Profinite.NobelingProof.ProjRestricts_coe`：∀ {I : Type u} (C : Set (I → 
Bool)) {J K : I → Prop} [inst : (i : I) → Decidable (J i)]   [inst_1 : (i : I) →
 Decidable (K i)] (h : ∀ (i : I…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Profinite.NobelingProof.ProjRestrict_coe`：∀ {I : Type u} (C : Set (I → B
ool)) (J : I → Prop) [inst : (i : I) → Decidable (J i)] (a : ↑C) (a_1 : I),   ↑(
Profinite.NobelingProof.ProjRe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.if_false_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p th
en t else false) = (decide p && t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  simp_all

variable (J)

/-- The objectwise map in the isomorphism `spanFunctor ≅ Profinite.indexFunctor`. -/
/-
**Profinite.NobelingProof.iso_map** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingP
roof`。
形式化陈述：iso_map : C(π C J, (IndexFunctor.obj C J))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The objectwise map in the isomorphism `spanFunctor ≅ Profinite.indexFunctor`.
-/
def iso_map : C(π C J, (IndexFunctor.obj C J)) :=
  ⟨fun x ↦ ⟨fun i ↦ x.val i.val, by
    rcases x with ⟨x, y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext ⟨i, hi⟩
    simp [precomp, Proj, hi]⟩, by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    exact (continuous_apply i.val).comp continuous_subtype_val⟩
/-
**Profinite.NobelingProof.iso_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Profinite
.NobelingProof`。
形式化陈述：iso_map_bijective : Function.Bijective (iso_map C J)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma iso_map_bijective : Function.Bijective (iso_map C J) := by
  refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · ext i
    rw [Subtype.ext_iff] at h
    by_cases hi : J i
    · exact congr_fun h ⟨i, hi⟩
    · rcases a with ⟨_, c, hc, rfl⟩
      rcases b with ⟨_, d, hd, rfl⟩
      simp only [Proj, if_neg hi]
  · refine ⟨⟨fun i ↦ if hi : J i then a.val ⟨i, hi⟩ else false, ?_⟩, ?_⟩
    · rcases a with ⟨_, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · ext i
      exact dif_pos i.prop

variable {C}

/--
For a given compact subset `C` of `I → Bool`, `spanFunctor` is the functor from the poset of finsets
of `I` to `Profinite`, sending a finite subset set `J` to the image of `C` under the projection
`Proj J`.
-/
noncomputable
/-
**Profinite.NobelingProof.spanFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobel
ingProof`。
形式化陈述：spanFunctor [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCo
mpact C) : (Finset I)ᵒᵖ ⥤ Profinite.{u} where obj s
参数：s : Finset I；i : I；i in s；hC : IsCompact C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def spanFunctor [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    (Finset I)ᵒᵖ ⥤ Profinite.{u} where
  obj s := @Profinite.of (π C (· ∈ (unop s))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := @CompHausLike.ofHom _ _ _ (_) (_) (_) (_) (_) (_) (_) (_)
    ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by simp only [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by rw [← CompHausLike.ofHom_comp]; congr; dsimp; rw [projRestricts_eq_comp]

/-- The limit cone on `spanFunctor` with point `C`. -/
noncomputable
/-
**Profinite.NobelingProof.spanCone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobeling
Proof`。
形式化陈述：spanCone [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompa
ct C) : Cone (spanFunctor hC) where pt
参数：s : Finset I；i : I；i in s；hC : IsCompact C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def spanCone [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    Cone (spanFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app s := ConcreteCategory.ofHom ⟨ProjRestrict C (· ∈ unop s), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_map,
        ← projRestricts_comp_projRestrict C (leOfHom h.unop)]
      rfl }

/-- The isomorphism `spanFunctor hC ≅ indexFunctor hC` when `hC : IsCompact C`. -/
@[simps!]
/-
**Profinite.NobelingProof.spanFunctorIsoIndexFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
Profinite.NobelingProof`。
形式化陈述：spanFunctorIsoIndexFunctor [forall (s : Finset I) (i : I), Decidable (i in
 s)] (hC : IsCompact C) : spanFunctor hC ≅ indexFunctor hC
参数：s : Finset I；i : I；i in s；hC : IsCompact C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `spanFunctor hC ≅ indexFunctor hC` when `hC : IsCompact C`.
-/
noncomputable def spanFunctorIsoIndexFunctor
    [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    spanFunctor hC ≅ indexFunctor hC :=
  NatIso.ofComponents
    (fun s ↦ CompHausLike.isoOfBijective (ConcreteCategory.ofHom (iso_map C (· ∈ unop s)))
      (iso_map_bijective C (· ∈ unop s))) (by
        rintro ⟨s⟩ ⟨t⟩ ⟨⟨⟨f⟩⟩⟩
        ext x
        have : iso_map C (· ∈ t) ∘ ProjRestricts C f =
            IndexFunctor.map C f ∘ iso_map C (· ∈ s) := by
          ext _ i; exact dif_pos i.prop
        exact congr_fun this x)

/-- `spanCone` is a limit cone. -/
noncomputable
/-
**Profinite.NobelingProof.spanCone_isLimit** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.
NobelingProof`。
形式化陈述：spanCone_isLimit [forall (s : Finset I) (i : I), Decidable (i in s)] (hC :
 IsCompact C) : CategoryTheory.Limits.IsLimit (spanCone hC)
参数：s : Finset I；i : I；i in s；hC : IsCompact C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def spanCone_isLimit [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    CategoryTheory.Limits.IsLimit (spanCone hC) :=
  IsLimit.postcomposeHomEquiv (spanFunctorIsoIndexFunctor hC) _
    (IsLimit.ofIsoLimit (indexCone_isLimit hC) (Cone.ext (Iso.refl _) (fun ⟨s⟩ ↦ by
      ext
      have : iso_map C (· ∈ s) ∘ ProjRestrict C (· ∈ s) = IndexFunctor.π_app C (· ∈ s) := by
        ext _ i; exact dif_pos i.prop
      exact congr_fun this.symm _)))

end Projections

section Products
/-!
## Defining the basis

Our proposed basis consists of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be
written as linear combinations of lexicographically smaller products. See below for the definition
of `e`.

### Main definitions

* For `i : I`, we let `e C i : LocallyConstant C ℤ` denote the map
  `fun f ↦ (if f.val i then 1 else 0)`.

* `Products I` is the type of lists of decreasing elements of `I`, so a typical element is
  `[i₁, i₂,..., iᵣ]` with `i₁ > i₂ > ... > iᵣ`.

* `Products.eval C` is the `C`-evaluation of a list. It takes a term `[i₁, i₂,..., iᵣ] : Products I`
  and returns the actual product `e C i₁ ··· e C iᵣ : LocallyConstant C ℤ`.

* `GoodProducts C` is the set of `Products I` such that their `C`-evaluation cannot be written as
  a linear combination of evaluations of lexicographically smaller lists.

### Main results

* `Products.evalFacProp` and `Products.evalFacProps` establish the fact that `Products.eval`
  interacts nicely with the projection maps from the previous section.

* `GoodProducts.span_iff_products`: the good products span `LocallyConstant C ℤ` iff all the
  products span `LocallyConstant C ℤ`.
-/

/--
`e C i` is the locally constant map from `C : Set (I → Bool)` to `ℤ` sending `f` to 1 if
`f.val i = true`, and 0 otherwise.
-/
/-
**Profinite.NobelingProof.e** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`。
形式化陈述：e (i : I) : LocallyConstant C Int where toFun
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`e C i` is the locally constant map from `C : Set (I → Bool)` to `ℤ` sending `f`
 to 1 if
`f.val i = true`, and 0 otherwise.
-/
def e (i : I) : LocallyConstant C ℤ where
  toFun := fun f ↦ (if f.val i then 1 else 0)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun (a : Bool) ↦ (if a then (1 : ℤ) else 0))).comp
      ((continuous_apply i).comp continuous_subtype_val)

variable [LinearOrder I]

/--
`Products I` is the type of lists of decreasing elements of `I`, so a typical element is
`[i₁, i₂, ...]` with `i₁ > i₂ > ...`. We order `Products I` lexicographically, so `[] < [i₁, ...]`,
and `[i₁, i₂, ...] < [j₁, j₂, ...]` if either `i₁ < j₁`, or `i₁ = j₁` and `[i₂, ...] < [j₂, ...]`.

Terms `m = [i₁, i₂, ..., iᵣ]` of this type will be used to represent products of the form
`e C i₁ ··· e C iᵣ : LocallyConstant C ℤ` . The function associated to `m` is `m.eval`.
-/
/-
**Profinite.NobelingProof.Products** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobeling
Proof`。
形式化陈述：Products (I : Type*) [LinearOrder I]
参数：I : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Products I` is the type of lists of decreasing elements of `I`, so a typical el
ement is
`[i₁, i₂, ...]` with `i₁ > i₂ > ...`. We order `Products I` lexicographically, s
o `[] < [i₁, ...]`,
and `[i₁, i₂, ...] < [j₁, j₂, ...]` if either `i₁ < j₁`, or `i₁ = j₁` and `[i₂, 
...] < [j₂, ...]`.

Terms `m = [i₁, i₂, ..., iᵣ]` of this type will be used to represent products of
 the form
`e C i₁ ··· e C iᵣ : LocallyConstant C ℤ` . The function associated to `m` is `m
.eval`.
-/
def Products (I : Type*) [LinearOrder I] := {l : List I // l.IsChain (· > ·)}

namespace Products

/-
**Profinite.NobelingProof.Products.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.Nobelin
gProof.Products`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder (Products I) :=
  inferInstanceAs (LinearOrder {l : List I // l.IsChain (· > ·)})

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Profinite.NobelingProof.Products.lt_iff_lex_lt** 是 Mathlib 中的一个定理，位于命名空间 `Prof
inite.NobelingProof.Products`。
形式化陈述：lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (· < ·) l.val m.val
参数：l m : Products I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (· < ·) l.val m.val := by
  simp
/-
**Profinite.NobelingProof.Products.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.Nobelin
gProof.Products`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedLT I] : WellFoundedLT (Products I) := by
  have : (· < · : Products I → _ → _) = (fun l m ↦ List.Lex (· < ·) l.val m.val) := by
    ext; exact lt_iff_lex_lt _ _
  rw [WellFoundedLT, this]
  dsimp [Products]
  rw [(by rfl : (· > · : I → _) = flip (· < ·))]
  infer_instance

/-- The evaluation `e C i₁ ··· e C iᵣ : C → ℤ` of a formal product `[i₁, i₂, ..., iᵣ]`. -/
/-
**Profinite.NobelingProof.Products.eval** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nob
elingProof.Products`。
形式化陈述：eval (l : Products I)
参数：l : Products I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation `e C i₁ ··· e C iᵣ : C → ℤ` of a formal product `[i₁, i₂, ..., iᵣ
]`.
-/
def eval (l : Products I) := (l.1.map (e C)).prod

/--
The predicate on products which we prove picks out a basis of `LocallyConstant C ℤ`. We call such a
product "good".
-/
/-
**Profinite.NobelingProof.Products.isGood** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.N
obelingProof.Products`。
形式化陈述：isGood (l : Products I) : Prop
参数：l : Products I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate on products which we prove picks out a basis of `LocallyConstant C
 ℤ`. We call such a
product "good".
-/
def isGood (l : Products I) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})
/-
**Profinite.NobelingProof.Products.rel_head** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof.Products`。
形式化陈述：rel_head!_of_mem [Inhabited I] {i : I} {l : Products I} (hi : i in l.val) 
: i <= l.val.head!
参数：hi : i in l.val。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rel_head!_of_mem [Inhabited I] {i : I} {l : Products I} (hi : i ∈ l.val) :
    i ≤ l.val.head! :=
  List.Pairwise.head!_le l.2.sortedGT.sortedGE.pairwise hi
/-
**Profinite.NobelingProof.Products.head** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nob
elingProof.Products`。
形式化陈述：head!_le_of_lt [Inhabited I] {q l : Products I} (h : q < l) (hq : q.val !=
 []) : q.val.head! <= l.val.head!
参数：h : q < l；hq : q.val != []。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_le_of_lt [Inhabited I] {q l : Products I} (h : q < l) (hq : q.val ≠ []) :
    q.val.head! ≤ l.val.head! :=
  List.head!_le_of_lt l.val q.val h hq

end Products

/-- The set of good products. -/
/-
**Profinite.NobelingProof.GoodProducts** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：GoodProducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of good products.
-/
def GoodProducts := {l : Products I | l.isGood C}

namespace GoodProducts

/-- Evaluation of good products. -/
/-
**Profinite.NobelingProof.GoodProducts.eval** 是 Mathlib 中的一个定义，位于命名空间 `Profinite
.NobelingProof.GoodProducts`。
形式化陈述：eval (l : {l : Products I // l.isGood C}) : LocallyConstant C Int
参数：l : {l : Products I // l.isGood C}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of good products.
-/
def eval (l : {l : Products I // l.isGood C}) : LocallyConstant C ℤ :=
  Products.eval C l.1
/-
**Profinite.NobelingProof.GoodProducts.injective** 是 Mathlib 中的一个定理，位于命名空间 `Prof
inite.NobelingProof.GoodProducts`。
形式化陈述：injective : Function.Injective (eval C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem injective : Function.Injective (eval C) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  dsimp [eval] at h
  by_contra! hne
  cases hne.lt_or_gt with
  | inl h' => apply hb; rw [← h]; exact Submodule.subset_span ⟨a, h', rfl⟩
  | inr h' => apply ha; rw [h]; exact Submodule.subset_span ⟨b, h', rfl⟩

/-- The image of the good products in the module `LocallyConstant C ℤ`. -/
/-
**Profinite.NobelingProof.GoodProducts.range** 是 Mathlib 中的一个定义，位于命名空间 `Profinit
e.NobelingProof.GoodProducts`。
形式化陈述：range
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of the good products in the module `LocallyConstant C ℤ`.
-/
def range := Set.range (GoodProducts.eval C)

/-- The type of good products is equivalent to its image. -/
noncomputable
/-
**Profinite.NobelingProof.GoodProducts.equiv_range** 是 Mathlib 中的一个定义，位于命名空间 `Pr
ofinite.NobelingProof.GoodProducts`。
形式化陈述：equiv_range : GoodProducts C ≃ range C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.GoodProducts.injective`：injective : Function.Inj
ective (eval C)
-/
def equiv_range : GoodProducts C ≃ range C :=
  Equiv.ofInjective (eval C) (injective C)
/-
**Profinite.NobelingProof.GoodProducts.equiv_toFun_eq_eval** 是 Mathlib 中的一个定理，位于
命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：equiv_toFun_eq_eval : (equiv_range C).toFun = Set.rangeFactorization (eval
 C)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_toFun_eq_eval : (equiv_range C).toFun = Set.rangeFactorization (eval C) := rfl
/-
**Profinite.NobelingProof.GoodProducts.linearIndependent_iff_range** 是 Mathlib 中
的一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：linearIndependent_iff_range : LinearIndependent Int (GoodProducts.eval C) 
↔ LinearIndependent Int (fun (p : range C) => p.1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.rangeFactorization_eq`：rangeFactorization_eq {f : ι -> β} : Subtype.
val ∘ rangeFactorization f = f
· 使用定理 `Profinite.NobelingProof.GoodProducts.equiv_toFun_eq_eval`：equiv_toFun_eq
_eval : (equiv_range C).toFun = Set.rangeFactorization (eval C)
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
theorem linearIndependent_iff_range : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : range C) ↦ p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C), ← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_range C)

end GoodProducts

namespace Products

set_option backward.defeqAttrib.useBackward true in
/-
**Profinite.NobelingProof.Products.eval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.
NobelingProof.Products`。
形式化陈述：eval_eq (l : Products I) (x : C) : l.eval C x = if forall i, i in l.val ->
 (x.val i = true) then 1 else 0
参数：l : Products I；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.Products.eval.eq_1`：∀ {I : Type u} (C : Set (I →
 Bool)) [inst : LinearOrder I] (l : Profinite.NobelingProof.Products I),   Profi
nite.NobelingProof.Products.eval…
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.prod_eq_one`：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, (∀ x 
∈ l, x = 1) → l.prod = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
-/
theorem eval_eq (l : Products I) (x : C) :
    l.eval C x = if ∀ i, i ∈ l.val → (x.val i = true) then 1 else 0 := by
  change LocallyConstant.evalMonoidHom x (l.eval C) = _
  rw [eval, map_list_prod]
  split_ifs with h
  · simp only [List.map_map]
    apply List.prod_eq_one
    simp only [List.mem_map, Function.comp_apply]
    rintro _ ⟨i, hi, rfl⟩
    exact if_pos (h i hi)
  · simp only [List.map_map, List.prod_eq_zero_iff, List.mem_map, Function.comp_apply]
    push Not at h
    convert! h with i
    dsimp [LocallyConstant.evalMonoidHom, e]
    simp only [ite_eq_right_iff, one_ne_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.Products.evalFacProp** 是 Mathlib 中的一个定理，位于命名空间 `Profin
ite.NobelingProof.Products`。
形式化陈述：evalFacProp {l : Products I} (J : I -> Prop) (h : forall a, a in l.val -> 
J a) [forall j, Decidable (J j)] : l.eval (π C J) ∘ ProjRestrict C J = l.eval C
参数：J : I -> Prop；h : forall a, a in l.val -> J a；J j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.Products.eval_eq`：eval_eq (l : Products I) (x : 
C) : l.eval C x = if forall i, i in l.val -> (x.val i = true) then 1 else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalFacProp {l : Products I} (J : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] :
    l.eval (π C J) ∘ ProjRestrict C J = l.eval C := by
  ext x
  dsimp only [ProjRestrict, Function.comp_apply]
  rw [Products.eval_eq, Products.eval_eq]
  simp +contextual [h, Proj]
/-
**Profinite.NobelingProof.Products.evalFacProps** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof.Products`。
形式化陈述：evalFacProps {l : Products I} (J K : I -> Prop) (h : forall a, a in l.val 
-> J a) [forall j, Decidable (J j)] [forall j, Decidable (K j)] (hJK : forall i,
 J i -> K i) : l.eval (π C J) ∘ ProjRestricts C hJK = l.eval (π C K)
参数：J K : I -> Prop；h : forall a, a in l.val -> J a；J j；K j；hJK : forall i, J i -
> K i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.proj_eq_of_subset`：proj_eq_of_subset (h : forall
 i, J i -> K i) : π (π C K) J = π C J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.setCongr_apply`：∀ {α : Type u_3} {s t : Set α} (h : s = t) (a : { 
a // (fun x => x ∈ s) a }), (Equiv.setCongr h) a = ⟨↑a, ⋯⟩
· 使用定理 `Profinite.NobelingProof.Products.eval_eq`：eval_eq (l : Products I) (x : 
C) : l.eval C x = if forall i, i in l.val -> (x.val i = true) then 1 else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Profinite.NobelingProof.ProjRestricts.eq_1`：∀ {I : Type u} (C : Set (I →
 Bool)) {J K : I → Prop} [inst : (i : I) → Decidable (J i)]   [inst_1 : (i : I) 
→ Decidable (K i)] (h : ∀ (i : I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Profinite.NobelingProof.Products.evalFacProp`：evalFacProp {l : Products 
I} (J : I -> Prop) (h : forall a, a in l.val -> J a) [forall j, Decidable (J j)]
 : l.eval (π C J) ∘ ProjRestrict C…
-/
theorem evalFacProps {l : Products I} (J K : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] [∀ j, Decidable (K j)]
    (hJK : ∀ i, J i → K i) :
    l.eval (π C J) ∘ ProjRestricts C hJK = l.eval (π C K) := by
  have : l.eval (π C J) ∘ Homeomorph.setCongr (proj_eq_of_subset C J K hJK) =
      l.eval (π (π C K) J) := by
    ext; simp [Homeomorph.setCongr, Products.eval_eq]
  rw [ProjRestricts, ← Function.comp_assoc, this, ← evalFacProp (π C K) J h]
/-
**Profinite.NobelingProof.Products.prop_of_isGood** 是 Mathlib 中的一个定理，位于命名空间 `Pro
finite.NobelingProof.Products`。
形式化陈述：prop_of_isGood {l : Products I} (J : I -> Prop) [forall j, Decidable (J j)
] (h : l.isGood (π C J)) : forall a, a in l.val -> J a
参数：J : I -> Prop；J j；h : l.isGood (π C J)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.Products.eval_eq`：eval_eq (l : Products I) (x : 
C) : l.eval C x = if forall i, i in l.val -> (x.val i = true) then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `LocallyConstant.zero_apply`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topo
logicalSpace X] [inst_1 : Zero Y] (x : X), 0 x = 0
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
theorem prop_of_isGood {l : Products I} (J : I → Prop) [∀ j, Decidable (J j)]
    (h : l.isGood (π C J)) : ∀ a, a ∈ l.val → J a := by
  intro i hi
  by_contra h'
  apply h
  suffices eval (π C J) l = 0 by
    rw [this]
    exact Submodule.zero_mem _
  ext ⟨_, _, _, rfl⟩
  rw [eval_eq, if_neg fun h ↦ ?_, LocallyConstant.zero_apply]
  simpa [Proj, h'] using h i hi

end Products

/-- The good products span `LocallyConstant C ℤ` if and only all the products do. -/
/-
**Profinite.NobelingProof.GoodProducts.span_iff_products** 是 Mathlib 中的一个定理，位于命名
空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [WellFoundedLT 
I],   ⊤ ≤ Submodule.span ℤ (Set.range (Profinite.NobelingProof.GoodProducts.eval
 C)) ↔     ⊤ ≤ Submodule.span ℤ (Set.range (Profinite.NobelingProof.Products.eva
l C))
参数：C : Set (I → Bool)；Set.range (Profinite.NobelingProof.GoodProducts.eval C)；Se
t.range (Profinite.NobelingProof.Products.eval C)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a
· 使用定理 `Profinite.NobelingProof.Products.instWellFoundedLT`：∀ {I : Type u} [inst
 : LinearOrder I] [WellFoundedLT I], WellFoundedLT (Profinite.NobelingProof.Prod
ucts I)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The good products span `LocallyConstant C ℤ` if and only all the products do.
-/
theorem GoodProducts.span_iff_products [WellFoundedLT I] :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) ↔
      ⊤ ≤ Submodule.span ℤ (Set.range (Products.eval C)) := by
  refine ⟨fun h ↦ le_trans h (span_mono (fun a ⟨b, hb⟩ ↦ ⟨b.val, hb⟩)), fun h ↦ le_trans h ?_⟩
  rw [span_le]
  rintro f ⟨l, rfl⟩
  let L : Products I → Prop := fun m ↦ m.eval C ∈ span ℤ (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (· < · : Products I → Products I → Prop)
  intro l h
  by_cases hl : l.isGood C
  · apply subset_span
    exact ⟨⟨l, hl⟩, rfl⟩
  · simp only [Products.isGood, not_not] at hl
    suffices Products.eval C '' {m | m < l} ⊆ span ℤ (Set.range (GoodProducts.eval C)) by
      rw [← span_le] at this
      exact this hl
    rintro a ⟨m, hm, rfl⟩
    exact h m hm

end Products

variable [LinearOrder I] [WellFoundedLT I]

section Ordinal
/-!
## Relating elements of the well-order `I` with ordinals

We choose a well-ordering on `I`. This amounts to regarding `I` as an ordinal, and as such it
can be regarded as the set of all strictly smaller ordinals, allowing to apply ordinal induction.

### Main definitions

* `ord I i` is the term `i` of `I` regarded as an ordinal.

* `term I ho` is a sufficiently small ordinal regarded as a term of `I`.

* `contained C o` is a predicate saying that `C` is "small" enough in relation to the ordinal `o`
  to satisfy the inductive hypothesis.

* `P I` is the predicate on ordinals about linear independence of good products, which the rest of
  this file is spent on proving by induction.
-/

variable (I)

/-- A term of `I` regarded as an ordinal. -/
/-
**Profinite.NobelingProof.ord** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof
`。
形式化陈述：ord (i : I) : Ordinal
参数：i : I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
A term of `I` regarded as an ordinal.
-/
def ord (i : I) : Ordinal := Ordinal.typein ((· < ·) : I → I → Prop) i

/-- An ordinal regarded as a term of `I`. -/
noncomputable
/-
**Profinite.NobelingProof.term** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProo
f`。
形式化陈述：term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)) : I
参数：ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
def term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I → I → Prop)) : I :=
  Ordinal.enum ((· < ·) : I → I → Prop) ⟨o, ho⟩

variable {I}
/-
**Profinite.NobelingProof.term_ord_aux** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：term_ord_aux {i : I} (ho : ord I i < Ordinal.type ((· < ·) : I -> I -> Pro
p)) : term I ho = i
参数：ho : ord I i < Ordinal.type ((· < ·) : I -> I -> Prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_ord_aux {i : I} (ho : ord I i < Ordinal.type ((· < ·) : I → I → Prop)) :
    term I ho = i := by
  simp only [term, ord, Ordinal.enum_typein]

@[simp]
/-
**Profinite.NobelingProof.ord_term_aux** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：ord_term_aux {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Pro
p)) : ord I (term I ho) = o
参数：ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ord_term_aux {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I → I → Prop)) :
    ord I (term I ho) = o := by
  simp only [ord, term, Ordinal.typein_enum]
/-
**Profinite.NobelingProof.ord_term** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeling
Proof`。
形式化陈述：ord_term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)) 
(i : I) : ord I i = o ↔ term I ho = i
参数：ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)；i : I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.term_ord_aux`：term_ord_aux {i : I} (ho : ord I i
 < Ordinal.type ((· < ·) : I -> I -> Prop)) : term I ho = i
· 使用定理 `Profinite.NobelingProof.ord_term_aux`：ord_term_aux {o : Ordinal} (ho : o
 < Ordinal.type ((· < ·) : I -> I -> Prop)) : ord I (term I ho) = o
-/
theorem ord_term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I → I → Prop)) (i : I) :
    ord I i = o ↔ term I ho = i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · subst h
    exact term_ord_aux ho
  · subst h
    exact ord_term_aux ho

/-- A predicate saying that `C` is "small" enough to satisfy the inductive hypothesis. -/
/-
**Profinite.NobelingProof.contained** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobelin
gProof`。
形式化陈述：contained (o : Ordinal) : Prop
参数：o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate saying that `C` is "small" enough to satisfy the inductive hypothesi
s.
-/
def contained (o : Ordinal) : Prop := ∀ f, f ∈ C → ∀ (i : I), f i = true → ord I i < o

variable (I) in
/--
The predicate on ordinals which we prove by induction, see `GoodProducts.P0`,
`GoodProducts.Plimit` and `GoodProducts.linearIndependentAux` in the section `Induction` below
-/
/-
**Profinite.NobelingProof.P** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`。
形式化陈述：P (o : Ordinal) : Prop
参数：o : Ordinal。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
The predicate on ordinals which we prove by induction, see `GoodProducts.P0`,
`GoodProducts.Plimit` and `GoodProducts.linearIndependentAux` in the section `In
duction` below
-/
def P (o : Ordinal) : Prop :=
  o ≤ Ordinal.type (· < · : I → I → Prop) →
  (∀ (C : Set (I → Bool)), IsClosed C → contained C o →
    LinearIndependent ℤ (GoodProducts.eval C))
/-
**Profinite.NobelingProof.Products.prop_of_isGood_of_contained** 是 Mathlib 中的一个定
理，位于命名空间 `Profinite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I]   {l : Profinite.NobelingProof.Products I} (o : Ordinal.{u}),   Prof
inite.NobelingProof.Products.isGood C l →     Profinite.NobelingProof.contained 
C o → ∀ i ∈ ↑l, Profinite.NobelingProof.ord I i < o
参数：C : Set (I → Bool)；o : Ordinal.{u}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.Products.eval_eq`：eval_eq (l : Products I) (x : 
C) : l.eval C x = if forall i, i in l.val -> (x.val i = true) then 1 else 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem Products.prop_of_isGood_of_contained {l : Products I} (o : Ordinal) (h : l.isGood C)
    (hsC : contained C o) (i : I) (hi : i ∈ l.val) : ord I i < o := by
  by_contra h'
  apply h
  suffices eval C l = 0 by simp [this]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

end Ordinal

section Maps
/-!
## `ℤ`-linear maps induced by projections

We define injective `ℤ`-linear maps between modules of the form `LocallyConstant C ℤ` induced by
precomposition with the projections defined in the section `Projections`.

### Main definitions

* `πs` and `πs'` are the `ℤ`-linear maps corresponding to `ProjRestrict` and `ProjRestricts`
  respectively.

### Main result

* We prove that `πs` and `πs'` interact well with `Products.eval` and the main application is the
  theorem `isGood_mono` which says that the property `isGood` is "monotone" on ordinals.
-/

/-
**Profinite.NobelingProof.contained_eq_proj** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof`。
形式化陈述：contained_eq_proj (o : Ordinal) (h : contained C o) : C = π C (ord I · < o
)
参数：o : Ordinal；h : contained C o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.proj_prop_eq_self`：proj_prop_eq_self (hh : foral
l i x, x in C -> x i != false -> J i) : π C J = C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)

--- 原说明 ---
## `ℤ`-linear maps induced by projections

We define injective `ℤ`-linear maps between modules of the form `LocallyConstant
 C ℤ` induced by
precomposition with the projections defined in the section `Projections`.

### Main definitions

* `πs` and `πs'` are the `ℤ`-linear maps corresponding to `ProjRestrict` and `Pr
ojRestricts`
  respectively.

### Main result

* We prove that `πs` and `πs'` interact well with `Products.eval` and the main a
pplication is the
  theorem `isGood_mono` which says that the property `isGood` is "monotone" on o
rdinals.
-/
theorem contained_eq_proj (o : Ordinal) (h : contained C o) :
    C = π C (ord I · < o) := by
  have := proj_prop_eq_self C (ord I · < o)
  simp only [ne_eq, Bool.not_eq_false, π] at this
  exact (this (fun i x hx ↦ h x hx i)).symm
/-
**Profinite.NobelingProof.isClosed_proj** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nob
elingProof`。
形式化陈述：isClosed_proj (o : Ordinal) (hC : IsClosed C) : IsClosed (π C (ord I · < o
))
参数：o : Ordinal；hC : IsClosed C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `Profinite.NobelingProof.continuous_proj`：continuous_proj : Continuous (P
roj J : (I -> Bool) -> (I -> Bool))
-/
theorem isClosed_proj (o : Ordinal) (hC : IsClosed C) : IsClosed (π C (ord I · < o)) :=
  (continuous_proj (ord I · < o)).isClosedMap C hC
/-
**Profinite.NobelingProof.contained_proj** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof`。
形式化陈述：contained_proj (o : Ordinal) : contained (π C (ord I · < o)) o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.if_false_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p th
en t else false) = (decide p && t)
· 使用定理 `Bool.and_eq_true`：∀ (a b : Bool), ((a && b) = true) = (a = true ∧ b = tr
ue)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem contained_proj (o : Ordinal) : contained (π C (ord I · < o)) o := by
  intro x ⟨_, _, h⟩ j hj
  aesop (add simp Proj)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (ord I · < o)`. -/
@[simps!]
noncomputable
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def πs (o : Ordinal) : LocallyConstant (π C (ord I · < o)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(ProjRestrict C (ord I · < o)), (continuous_projRestrict _ _)⟩
/-
**Profinite.NobelingProof.coe_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.NobelingProo
f`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_πs (o : Ordinal) (f : LocallyConstant (π C (ord I · < o)) ℤ) :
    πs C o f = f ∘ ProjRestrict C (ord I · < o) := by
  rfl
/-
**Profinite.NobelingProof.injective_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeli
ngProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem injective_πs (o : Ordinal) : Function.Injective (πs C o) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestrict _ _)⟩
    (Set.surjective_mapsTo_image_restrict _ _)

/-- The `ℤ`-linear map induced by precomposition of the projection
`π C (ord I · < o₂) → π C (ord I · < o₁)` for `o₁ ≤ o₂`. -/
@[simps!]
noncomputable
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    LocallyConstant (π C (ord I · < o₁)) ℤ →ₗ[ℤ] LocallyConstant (π C (ord I · < o₂)) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(ProjRestricts C (fun _ hh ↦ lt_of_lt_of_le hh h)),
    (continuous_projRestricts _ _)⟩
/-
**Profinite.NobelingProof.coe_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.NobelingProo
f`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) (f : LocallyConstant (π C (ord I · < o₁)) ℤ) :
    (πs' C h f).toFun = f.toFun ∘ (ProjRestricts C (fun _ hh ↦ lt_of_lt_of_le hh h)) := by
  rfl
/-
**Profinite.NobelingProof.injective_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeli
ngProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem injective_πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Function.Injective (πs' C h) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestricts _ _)⟩
    (surjective_projRestricts _ fun _ hi ↦ lt_of_lt_of_le hi h)

namespace Products

/-
**Profinite.NobelingProof.Products.lt_ord_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof.Products`。
形式化陈述：lt_ord_of_lt {l m : Products I} {o : Ordinal} (h₁ : m < l) (h₂ : forall i 
in l.val, ord I i < o) : forall i in m.val, ord I i < o
参数：h₁ : m < l；h₂ : forall i in l.val, ord I i < o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedGT.lt_ord_of_lt`：List.SortedGT.lt_ord_of_lt [LinearOrder α] [
WellFoundedLT α] {l m : List α} {o : Ordinal} (hl : l.SortedGT) (hm : m.SortedGT
) (hmltl : m < l…
· 使用定理 `List.IsChain.sortedGT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, List.IsChain (fun x1 x2 => x1 > x2) l → l.SortedGT
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lt_ord_of_lt {l m : Products I} {o : Ordinal} (h₁ : m < l)
    (h₂ : ∀ i ∈ l.val, ord I i < o) : ∀ i ∈ m.val, ord I i < o :=
  List.SortedGT.lt_ord_of_lt l.2.sortedGT m.2.sortedGT h₁ h₂
/-
**Profinite.NobelingProof.Products.eval_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof.Products`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_πs {l : Products I} {o : Ordinal} (hlt : ∀ i ∈ l.val, ord I i < o) :
    πs C o (l.eval (π C (ord I · < o))) = l.eval C := by
  simpa only [← LocallyConstant.coe_inj] using! evalFacProp C (ord I · < o) hlt
/-
**Profinite.NobelingProof.Products.eval_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof.Products`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_πs' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlt : ∀ i ∈ l.val, ord I i < o₁) :
    πs' C h (l.eval (π C (ord I · < o₁))) = l.eval (π C (ord I · < o₂)) := by
  rw [← LocallyConstant.coe_inj, ← LocallyConstant.toFun_eq_coe]
  exact evalFacProps C (fun (i : I) ↦ ord I i < o₁) (fun (i : I) ↦ ord I i < o₂) hlt
    (fun _ hh ↦ lt_of_lt_of_le hh h)
/-
**Profinite.NobelingProof.Products.eval_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof.Products`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_πs_image {l : Products I} {o : Ordinal}
    (hl : ∀ i ∈ l.val, ord I i < o) : eval C '' { m | m < l } =
    (πs C o) '' eval (π C (ord I · < o)) '' { m | m < l } := by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]
/-
**Profinite.NobelingProof.Products.eval_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof.Products`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_πs_image' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : ∀ i ∈ l.val, ord I i < o₁) : eval (π C (ord I · < o₂)) '' { m | m < l } =
    (πs' C h) '' eval (π C (ord I · < o₁)) '' { m | m < l } := by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]
/-
**Profinite.NobelingProof.Products.head_lt_ord_of_isGood** 是 Mathlib 中的一个定理，位于命名
空间 `Profinite.NobelingProof.Products`。
形式化陈述：head_lt_ord_of_isGood [Inhabited I] {l : Products I} {o : Ordinal} (h : l.
isGood (π C (ord I · < o))) (hn : l.val != []) : ord I (l.val.head!) < o
参数：h : l.isGood (π C (ord I · < o))；hn : l.val != []。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `List.head!_mem_self`：∀ {α : Type u} [inst : Inhabited α] {l : List α}, l
 ≠ [] → l.head! ∈ l
-/
theorem head_lt_ord_of_isGood [Inhabited I] {l : Products I} {o : Ordinal}
    (h : l.isGood (π C (ord I · < o))) (hn : l.val ≠ []) : ord I (l.val.head!) < o :=
  prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

/--
If `l` is good w.r.t. `π C (ord I · < o₁)` and `o₁ ≤ o₂`, then it is good w.r.t.
`π C (ord I · < o₂)`
-/
/-
**Profinite.NobelingProof.Products.isGood_mono** 是 Mathlib 中的一个定理，位于命名空间 `Profin
ite.NobelingProof.Products`。
形式化陈述：isGood_mono {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : l.isGo
od (π C (ord I · < o₁))) : l.isGood (π C (ord I · < o₂))
参数：h : o₁ <= o₂；hl : l.isGood (π C (ord I · < o₁))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.apply_mem_span_image_iff_mem_span`：apply_mem_span_image_iff_me
m_span [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {x : M} {s : Set M} (hf : Fu
nction.Injective f) : f x in Subm…
· 使用定理 `Profinite.NobelingProof.injective_πs'`：injective_πs' {o₁ o₂ : Ordinal} (
h : o₁ <= o₂) : Function.Injective (πs' C h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.eval_πs'`：eval_πs' {l : Products I} {o₁
 o₂ : Ordinal} (h : o₁ <= o₂) (hlt : forall i in l.val, ord I i < o₁) : πs' C h 
(l.eval (π C (ord I · < o₁))) =…
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `Profinite.NobelingProof.Products.eval_πs_image'`：eval_πs_image' {l : Pro
ducts I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : forall i in l.val, ord I i < o₁)
 : eval (π C (ord I · < o₂)) '' { m |…

--- 原说明 ---
If `l` is good w.r.t. `π C (ord I · < o₁)` and `o₁ ≤ o₂`, then it is good w.r.t.
`π C (ord I · < o₂)`
-/
theorem isGood_mono {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (π C (ord I · < o₁))) : l.isGood (π C (ord I · < o₂)) := by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood C _ hl), ← eval_πs' C h (prop_of_isGood C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

end Products

end Maps

end Profinite.NobelingProof

