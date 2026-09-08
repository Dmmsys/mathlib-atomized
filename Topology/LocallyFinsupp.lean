/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.Peel

/-!
# Type of functions with locally finite support

This file defines functions with locally finite support, provides supporting API. For suitable
targets, it establishes functions with locally finite support as an instance of a lattice ordered
commutative group.

Throughout the present file, `X` denotes a topologically space and `U` a subset of `X`.
-/

@[expose] public section

open Filter Function Set Topology

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

/-!
## Definition, coercion to functions and basic extensionality lemmas

A function with locally finite support within `U` is a function `X → Y` whose support is locally
finite within `U` and entirely contained in `U`.  For T1-spaces, the theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that the first condition is equivalent to the
condition that the support `f` is discrete within `U`.
-/

variable (U Y) in
/-- A function with locally finite support within `U` is a triple as specified below. -/
/-
**Function.locallyFinsuppWithin** 是 Mathlib 中的一个归纳类型，位于命名空间 `Function`。
形式化陈述：{X : Type u_1} → [TopologicalSpace X] → Set X → (Y : Type u_2) → [Zero Y] 
→ Type (max u_1 u_2)
参数：Y : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function with locally finite support within `U` is a triple as specified below
.
-/
structure Function.locallyFinsuppWithin [Zero Y] where
  /-- A function `X → Y` -/
  toFun : X → Y
  /-- A proof that the support of `toFun` is contained in `U` -/
  supportWithinDomain' : toFun.support ⊆ U
  /-- A proof that the support is locally finite within `U` -/
  supportLocallyFiniteWithinDomain' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ toFun.support)

variable (X Y) in
/--
A function with locally finite support is a function with locally finite support within
`⊤ : Set X`.
-/
/-
**Function.locallyFinsupp** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.locallyFinsupp [Zero Y]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function with locally finite support is a function with locally finite support
 within
`⊤ : Set X`.
-/
abbrev Function.locallyFinsupp [Zero Y] := locallyFinsuppWithin (Set.univ : Set X) Y

/--
Function with locally finite support have a zero.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function with locally finite support have a zero.
-/
instance [Zero Y] : Zero (locallyFinsuppWithin U Y) where
  zero :=
    { toFun := fun _ ↦ 0
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' z hz := by
        simp_rw [support_fun_zero, inter_empty, finite_empty, and_true]
        use Set.univ, univ_mem }

/--
For T1 spaces, the condition `supportLocallyFiniteWithinDomain'` is equivalent to saying that the
support is codiscrete within `U`.
-/
/-
**supportDiscreteWithin_iff_locallyFiniteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supportDiscreteWithin_iff_locallyFiniteWithin [T1Space X] [Zero Y] {f : X 
-> Y} (h : f.support subseteq U) : f =ᶠ[codiscreteWithin U] 0 ↔ forall z in U, e
xists t in 𝓝 z, Set.Finite (t inter f.support)
参数：h : f.support subseteq U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `codiscreteWithin_iff_locallyFiniteComplementWithin`：codiscreteWithin_iff
_locallyFiniteComplementWithin [T1Space X] {s U : Set X} : s in codiscreteWithin
 U ↔ forall z in U, exists t in 𝓝 z, Set…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
For T1 spaces, the condition `supportLocallyFiniteWithinDomain'` is equivalent t
o saying that the
support is codiscrete within `U`.
-/
theorem supportDiscreteWithin_iff_locallyFiniteWithin [T1Space X] [Zero Y] {f : X → Y}
    (h : f.support ⊆ U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : X → Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, mem_ofPred_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin, this]

/--
A function `f : X → Y` has locally finite support if for every `z : X`, there is a
neighbourhood `t` around `z` such that `t ∩ f.support` is finite.
-/
/-
**LocallyFiniteSupport** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteSupport [Zero Y] (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` has locally finite support if for every `z : X`, there is
 a
neighbourhood `t` around `z` such that `t ∩ f.support` is finite.
-/
def LocallyFiniteSupport [Zero Y] (f : X → Y) : Prop :=
  ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)
/-
**LocallyFiniteSupport.iff_locallyFinite_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteSupport.iff_locallyFinite_support [Zero Y] (f : X -> Y) : Loc
allyFinite (fun s : f.support => ({s.val} : Set X)) ↔ LocallyFiniteSupport f
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
-/
lemma LocallyFiniteSupport.iff_locallyFinite_support [Zero Y] (f : X → Y) :
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) ↔ LocallyFiniteSupport f := by
  dsimp only [LocallyFinite]
  peel with z t ht
  have aux1 : t ∩ f.support = {i : f.support | ↑i ∈ t} := by aesop
  have aux2 : InjOn Subtype.val {i : f.support | ↑i ∈ t} := by aesop
  simp only [singleton_inter_nonempty, aux1, finite_image_iff aux2]
/-
**LocallyFiniteSupport.locallyFinite_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteSupport.locallyFinite_support [Zero Y] (f : X -> Y) (h : Loca
llyFiniteSupport f) : LocallyFinite (fun s : f.support => ({s.val} : Set X))
参数：f : X -> Y；h : LocallyFiniteSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LocallyFiniteSupport.iff_locallyFinite_support`：LocallyFiniteSupport.iff
_locallyFinite_support [Zero Y] (f : X -> Y) : LocallyFinite (fun s : f.support 
=> ({s.val} : Set X)) ↔ LocallyFinit…
-/
lemma LocallyFiniteSupport.locallyFinite_support [Zero Y] (f : X → Y) (h : LocallyFiniteSupport f) :
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) :=
  (LocallyFiniteSupport.iff_locallyFinite_support f).mpr h
/-
**LocallyFiniteSupport.finite_inter_support_of_isCompact** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：LocallyFiniteSupport.finite_inter_support_of_isCompact {W : Set X} [Zero Y
] {f : X -> Y} (h : LocallyFiniteSupport f) (hW : IsCompact W) : (W inter f.supp
ort).Finite
参数：h : LocallyFiniteSupport f；hW : IsCompact W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.finite_nonempty_inter_compact`：finite_nonempty_inter_compa
ct {f : ι -> Set X} (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i inter
 s).Nonempty }.Finite
· 使用引理 `LocallyFiniteSupport.locallyFinite_support`：LocallyFiniteSupport.locally
Finite_support [Zero Y] (f : X -> Y) (h : LocallyFiniteSupport f) : LocallyFinit
e (fun s : f.support => ({s.val}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
lemma LocallyFiniteSupport.finite_inter_support_of_isCompact {W : Set X}
   [Zero Y] {f : X → Y} (h : LocallyFiniteSupport f)
   (hW : IsCompact W) : (W ∩ f.support).Finite := by
  have := LocallyFinite.finite_nonempty_inter_compact
    (LocallyFiniteSupport.locallyFinite_support f h) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} ∩ t).Nonempty} = (t ∩ s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this
/-
**Function.locallyFinsupp.locallyFiniteSupport** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.locallyFinsupp.locallyFiniteSupport [Zero Y] (f : locallyFinsupp 
X Y) : LocallyFiniteSupport f.toFun
参数：f : locallyFinsupp X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain'`：∀ {X : 
Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero 
Y]   (self : Function.locallyFinsuppWithin U Y), ∀ z …
-/
lemma Function.locallyFinsupp.locallyFiniteSupport [Zero Y] (f : locallyFinsupp X Y) :
    LocallyFiniteSupport f.toFun :=
  (f.supportLocallyFiniteWithinDomain' · (by trivial))

namespace Function.locallyFinsuppWithin

/--
Functions with locally finite support within `U` are `FunLike`: the coercion to functions is
injective.
-/
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functions with locally finite support within `U` are `FunLike`: the coercion to 
functions is
injective.
-/
instance [Zero Y] : FunLike (locallyFinsuppWithin U Y) X Y where
  coe D := D.toFun
  coe_injective := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ↦ by simp

@[simp]
/-
**Function.locallyFinsuppWithin.toFun_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Function
.locallyFinsuppWithin`。
形式化陈述：toFun_eq_coe [Zero Y] (c : locallyFinsuppWithin U Y) : c.toFun = ⇑c
参数：c : locallyFinsuppWithin U Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_eq_coe [Zero Y] (c : locallyFinsuppWithin U Y) : c.toFun = ⇑c := rfl

@[simp]
/-
**Function.locallyFinsuppWithin.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `Function.local
lyFinsuppWithin`。
形式化陈述：coe_mk [Zero Y] (f : X -> Y) (h : f.support subseteq U) (h' : forall z in 
U, exists t in 𝓝 z, Set.Finite (t inter f.support)) : ⇑(Function.locallyFinsuppW
ithin.mk f h h') = f
参数：f : X -> Y；h : f.support subseteq U；h' : forall z in U, exists t in 𝓝 z, Set.
Finite (t inter f.support)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk [Zero Y] (f : X → Y) (h : f.support ⊆ U)
    (h' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)) :
    ⇑(Function.locallyFinsuppWithin.mk f h h') = f := rfl

/-- This allows writing `D.support` instead of `Function.support D` -/
/-
**Function.locallyFinsuppWithin.support** 是 Mathlib 中的一个缩写定义，位于命名空间 `Function.lo
callyFinsuppWithin`。
形式化陈述：support [Zero Y] (D : locallyFinsuppWithin U Y)
参数：D : locallyFinsuppWithin U Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This allows writing `D.support` instead of `Function.support D`
-/
abbrev support [Zero Y] (D : locallyFinsuppWithin U Y) := Function.support D
/-
**Function.locallyFinsuppWithin.supportWithinDomain** 是 Mathlib 中的一个引理，位于命名空间 `F
unction.locallyFinsuppWithin`。
形式化陈述：supportWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : D.support su
bseteq U
参数：D : locallyFinsuppWithin U Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.locallyFinsuppWithin.supportWithinDomain'`：∀ {X : Type u_1} [in
st : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y]   (self : 
Function.locallyFinsuppWithin U Y), Func…
-/
lemma supportWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    D.support ⊆ U := D.supportWithinDomain'
/-
**Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain** 是 Mathlib 中的一
个引理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：supportLocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
 forall z in U, exists t in 𝓝 z, Set.Finite (t inter D.support)
参数：D : locallyFinsuppWithin U Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain'`：∀ {X : 
Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero 
Y]   (self : Function.locallyFinsuppWithin U Y), ∀ z …
-/
lemma supportLocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ D.support) := D.supportLocallyFiniteWithinDomain'

@[ext]
/-
**Function.locallyFinsuppWithin.ext** 是 Mathlib 中的一个引理，位于命名空间 `Function.locallyF
insuppWithin`。
形式化陈述：ext [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : forall a, D₁ a = D₂ a
) : D₁ = D₂
参数：h : forall a, D₁ a = D₂ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
lemma ext [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : ∀ a, D₁ a = D₂ a) :
    D₁ = D₂ := DFunLike.ext _ _ h
/-
**Function.locallyFinsuppWithin.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：coe_injective [Zero Y] : Injective (· : locallyFinsuppWithin U Y -> X -> Y
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma coe_injective [Zero Y] :
    Injective (· : locallyFinsuppWithin U Y → X → Y) := DFunLike.coe_injective

/-!
## Singleton Indicators as Functions with Locally Finite Support
-/

/--
Is analogy to `Finsupp.single`, this definition presents the indicator function
of a single point as a function with locally finite support.
-/
/-
**Function.locallyFinsuppWithin.single** 是 Mathlib 中的一个定义，位于命名空间 `Function.local
lyFinsuppWithin`。
形式化陈述：single [DecidableEq X] [Zero Y] (x : X) (y : Y) : locallyFinsupp X Y where
 toFun
参数：x : X；y : Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Is analogy to `Finsupp.single`, this definition presents the indicator function
of a single point as a function with locally finite support.
-/
noncomputable def single [DecidableEq X] [Zero Y] (x : X) (y : Y) : locallyFinsupp X Y where
  toFun := Pi.single x y
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, univ_mem, by simpa using (finite_singleton x).subset Pi.support_single_subset⟩

/--
Simplifier lemma: `single x y` takes the value `y` at `x` and is zero otherwise.
-/
/-
**Function.locallyFinsuppWithin.single_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function
.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {Y : Type u_2} [inst_1 : Deci
dableEq X] [inst_2 : Zero Y] {x₁ x₂ : X}   {y : Y}, (Function.locallyFinsuppWith
in.single x₁ y) x₂ = if x₂ = x₁ then y else 0
参数：Function.locallyFinsuppWithin.single x₁ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Simplifier lemma: `single x y` takes the value `y` at `x` and is zero otherwise.
-/
@[simp] lemma single_apply [DecidableEq X] [Zero Y] {x₁ x₂ : X} {y : Y} :
    single x₁ y x₂ = if x₂ = x₁ then y else 0 := by
  simp_rw [DFunLike.coe, single, Pi.single_apply]

/--
Simplifier lemma: `single x 0` is zero.
-/
/-
**Function.locallyFinsuppWithin.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.
locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {Y : Type u_2} [inst_1 : Deci
dableEq X] [inst_2 : Zero Y] {x : X},   Function.locallyFinsuppWithin.single x 0
 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a

--- 原说明 ---
Simplifier lemma: `single x 0` is zero.
-/
@[simp] lemma single_zero [DecidableEq X] [Zero Y] {x : X} :
    single x (0 : Y) = 0 := by aesop

/--
Simplifier lemma: coercion of `single x y` to a function.
-/
/-
**Function.locallyFinsuppWithin.coe_single** 是 Mathlib 中的一个定理，位于命名空间 `Function.l
ocallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {Y : Type u_2} [inst_1 : Deci
dableEq X] [inst_2 : Zero Y] {x : X} {y : Y},   ⇑(Function.locallyFinsuppWithin.
single x y) = Pi.single x y
参数：Function.locallyFinsuppWithin.single x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Simplifier lemma: coercion of `single x y` to a function.
-/
@[simp] lemma coe_single [DecidableEq X] [Zero Y] {x : X} {y : Y} :
    (single x y : X → Y) = Pi.single x y := by
  ext
  simp [Pi.single_apply]

/-!
## Elementary properties of the support
-/

/--
Simplifier lemma: Functions with locally finite support within `U` evaluate to zero outside of `U`.
-/
@[simp]
/-
**Function.locallyFinsuppWithin.apply_eq_zero_of_notMem** 是 Mathlib 中的一个引理，位于命名空
间 `Function.locallyFinsuppWithin`。
形式化陈述：apply_eq_zero_of_notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (h
z : z ∉ U) : D z = 0
参数：D : locallyFinsuppWithin U Y；hz : z ∉ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U

--- 原说明 ---
Simplifier lemma: Functions with locally finite support within `U` evaluate to z
ero outside of `U`.
-/
lemma apply_eq_zero_of_notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y)
    (hz : z ∉ U) :
    D z = 0 := notMem_support.mp fun a ↦ hz (D.supportWithinDomain a)

/--
On a T1 space, the support of a function with locally finite support within `U` is discrete within
`U`.
-/
/-
**Function.locallyFinsuppWithin.eq_zero_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名
空间 `Function.locallyFinsuppWithin`。
形式化陈述：eq_zero_codiscreteWithin [Zero Y] [T1Space X] (D : locallyFinsuppWithin U 
Y) : D =ᶠ[Filter.codiscreteWithin U] 0
参数：D : locallyFinsuppWithin U Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codiscreteWithin_iff_locallyFiniteComplementWithin`：codiscreteWithin_iff
_locallyFiniteComplementWithin [T1Space X] {s U : Set X} : s in codiscreteWithin
 U ↔ forall z in U, exists t in 𝓝 z, Set…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.support_subset_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zer
o M] {f : ι → M} {s : Set ι},   Function.support f ⊆ s ↔ ∀ (x : ι), f x ≠ 0 → x 
∈ s
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain`：supportL
ocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : forall z in U
, exists t in 𝓝 z, Set.Finite (t inter D.support)

--- 原说明 ---
On a T1 space, the support of a function with locally finite support within `U` 
is discrete within
`U`.
-/
theorem eq_zero_codiscreteWithin [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    D =ᶠ[Filter.codiscreteWithin U] 0 := by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  have : D.support = (U \ {x | D x = (0 : X → Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, Set.mem_ofPred_eq, iff_and_self]
    exact (support_subset_iff.1 D.supportWithinDomain) x
  rw [← this]
  exact D.supportLocallyFiniteWithinDomain

/--
On a T1 space, the support of a function with locally finite support within `U` is discrete.
-/
/-
**Function.locallyFinsuppWithin.discreteSupport** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.locallyFinsuppWithin`。
形式化陈述：discreteSupport [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) : IsDi
screte D.support
参数：D : locallyFinsuppWithin U Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `isDiscrete_of_codiscreteWithin`：isDiscrete_of_codiscreteWithin {U s : Se
t X} (h : sᶜ in Filter.codiscreteWithin U) : IsDiscrete (s inter U)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `supportDiscreteWithin_iff_locallyFiniteWithin`：supportDiscreteWithin_iff
_locallyFiniteWithin [T1Space X] [Zero Y] {f : X -> Y} (h : f.support subseteq U
) : f =ᶠ[codiscreteWithin U] 0 ↔ fo…
· 使用引理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain`：supportL
ocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : forall z in U
, exists t in 𝓝 z, Set.Finite (t inter D.support)

--- 原说明 ---
On a T1 space, the support of a function with locally finite support within `U` 
is discrete.
-/
theorem discreteSupport [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    IsDiscrete D.support := by
  have : D.support = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_ofPred_eq] at hx
      tauto
  rw [this]
  apply isDiscrete_of_codiscreteWithin
  rw [compl_compl]
  apply (supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
  exact D.supportLocallyFiniteWithinDomain

/--
If `X` is T1 and if `U` is closed, then the support of support of a function with locally finite
support within `U` is also closed.
-/
/-
**Function.locallyFinsuppWithin.closedSupport** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：closedSupport [T1Space X] [Zero Y] (D : locallyFinsuppWithin U Y) (hU : Is
Closed U) : IsClosed D.support
参数：D : locallyFinsuppWithin U Y；hU : IsClosed U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `isClosed_sdiff_of_codiscreteWithin`：isClosed_sdiff_of_codiscreteWithin {
s U : Set X} (hs : s in codiscreteWithin U) (hU : IsClosed U) : IsClosed (U \ s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `supportDiscreteWithin_iff_locallyFiniteWithin`：supportDiscreteWithin_iff
_locallyFiniteWithin [T1Space X] [Zero Y] {f : X -> Y} (h : f.support subseteq U
) : f =ᶠ[codiscreteWithin U] 0 ↔ fo…
· 使用引理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain`：supportL
ocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : forall z in U
, exists t in 𝓝 z, Set.Finite (t inter D.support)

--- 原说明 ---
If `X` is T1 and if `U` is closed, then the support of support of a function wit
h locally finite
support within `U` is also closed.
-/
theorem closedSupport [T1Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsClosed U) :
    IsClosed D.support := by
  convert!
    isClosed_sdiff_of_codiscreteWithin
      ((supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
        D.supportLocallyFiniteWithinDomain)
      hU
  ext x
  constructor <;> intro hx
  · simp_all [D.supportWithinDomain hx]
  · simp_all

/--
If `X` is T2 and if `U` is compact, then the support of a function with locally finite support
within `U` is finite.
-/
/-
**Function.locallyFinsuppWithin.finiteSupport** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：finiteSupport [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y) (hU : Is
Compact U) : Set.Finite D.support
参数：D : locallyFinsuppWithin U Y；hU : IsCompact U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.finite`：IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete 
s) : s.Finite
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `Function.locallyFinsuppWithin.closedSupport`：closedSupport [T1Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsClosed U) : IsClosed D.support
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `Function.locallyFinsuppWithin.discreteSupport`：discreteSupport [Zero Y] 
[T1Space X] (D : locallyFinsuppWithin U Y) : IsDiscrete D.support

--- 原说明 ---
If `X` is T2 and if `U` is compact, then the support of a function with locally 
finite support
within `U` is finite.
-/
theorem finiteSupport [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsCompact U) :
    Set.Finite D.support :=
  (hU.of_isClosed_subset (D.closedSupport hU.isClosed)
    D.supportWithinDomain).finite D.discreteSupport

/-!
## Lattice ordered group structure

If `X` is a suitable instance, this section equips functions with locally finite support within `U`
with the standard structure of a lattice ordered group, where addition, comparison, min and max are
defined pointwise.
-/

variable (U) in
/--
Functions with locally finite support within `U` form an additive submonoid of functions `X → Y`.
-/
/-
**Function.locallyFinsuppWithin.addSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Function
.locallyFinsuppWithin`。
形式化陈述：{X : Type u_1} → [TopologicalSpace X] → Set X → {Y : Type u_2} → [inst : A
ddMonoid Y] → AddSubmonoid (X → Y)
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functions with locally finite support within `U` form an additive submonoid of f
unctions `X → Y`.
-/
protected def addSubmonoid [AddMonoid Y] : AddSubmonoid (X → Y) where
  carrier := {f | f.support ⊆ U ∧ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)}
  zero_mem' := by
    simp only [support_subset_iff, ne_eq, mem_ofPred_eq, Pi.zero_apply, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, support_zero, inter_empty, finite_empty, and_true,
      true_and]
    exact fun _ _ ↦ ⟨⊤, univ_mem⟩
  add_mem' {f g} hf hg := by
    constructor
    · intro x hx
      contrapose hx
      simp [notMem_support.1 fun a ↦ hx (hf.1 a), notMem_support.1 fun a ↦ hx (hg.1 a)]
    · intro z hz
      obtain ⟨t₁, ht₁⟩ := hf.2 z hz
      obtain ⟨t₂, ht₂⟩ := hg.2 z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ f.support) ∪ (t₂ ∩ g.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [support_subset_iff, ne_eq, mem_ofPred_eq,
        mem_inter_iff, mem_support, Pi.add_apply, mem_union, true_and]
      by_contra! hCon
      simp_all
/-
**Function.locallyFinsuppWithin.memAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddMonoid Y]   (D : Function.locallyFinsuppWithin U Y), ⇑D ∈ Function.lo
callyFinsuppWithin.addSubmonoid U
参数：D : Function.locallyFinsuppWithin U Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用引理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain`：supportL
ocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : forall z in U
, exists t in 𝓝 z, Set.Finite (t inter D.support)
-/
protected lemma memAddSubmonoid [AddMonoid Y] (D : locallyFinsuppWithin U Y) :
    (D : X → Y) ∈ locallyFinsuppWithin.addSubmonoid U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

variable (U) in
/--
Functions with locally finite support within `U` form an additive subgroup of functions `X → Y`.
-/
/-
**Function.locallyFinsuppWithin.addSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Function.
locallyFinsuppWithin`。
形式化陈述：{X : Type u_1} → [TopologicalSpace X] → Set X → {Y : Type u_2} → [inst : A
ddGroup Y] → AddSubgroup (X → Y)
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functions with locally finite support within `U` form an additive subgroup of fu
nctions `X → Y`.
-/
protected def addSubgroup [AddGroup Y] : AddSubgroup (X → Y) where
  carrier := {f | f.support ⊆ U ∧ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)}
  __ := locallyFinsuppWithin.addSubmonoid U
  neg_mem' {f} hf := by simp_all
/-
**Function.locallyFinsuppWithin.memAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddGroup Y]   (D : Function.locallyFinsuppWithin U Y), ⇑D ∈ Function.loc
allyFinsuppWithin.addSubgroup U
参数：D : Function.locallyFinsuppWithin U Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用引理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain`：supportL
ocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : forall z in U
, exists t in 𝓝 z, Set.Finite (t inter D.support)
-/
protected lemma memAddSubgroup [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (D : X → Y) ∈ locallyFinsuppWithin.addSubgroup U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
/-
**Function.locallyFinsuppWithin.mk_of_mem_addSubmonoid** 是 Mathlib 中的一个定义，位于命名空间
 `Function.locallyFinsuppWithin`。
形式化陈述：mk_of_mem_addSubmonoid [AddMonoid Y] (f : X -> Y) (hf : f in locallyFinsup
pWithin.addSubmonoid U) : locallyFinsuppWithin U Y
参数：f : X -> Y；hf : f in locallyFinsuppWithin.addSubmonoid U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assign a function with locally finite support within `U` to a function in the su
bgroup.
-/
def mk_of_mem_addSubmonoid [AddMonoid Y] (f : X → Y)
    (hf : f ∈ locallyFinsuppWithin.addSubmonoid U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid Y] : Zero (locallyFinsuppWithin U Y) where
  zero := mk_of_mem_addSubmonoid 0 <| zero_mem _
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid Y] : Add (locallyFinsuppWithin U Y) where
  add D₁ D₂ := mk_of_mem_addSubmonoid (D₁ + D₂) <| add_mem D₁.memAddSubmonoid D₂.memAddSubmonoid
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid Y] : SMul ℕ (locallyFinsuppWithin U Y) where
  smul n D := mk_of_mem_addSubmonoid (n • D) <| nsmul_mem D.memAddSubmonoid n

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
/-
**Function.locallyFinsuppWithin.mk_of_mem_addSubgroup** 是 Mathlib 中的一个定义，位于命名空间 
`Function.locallyFinsuppWithin`。
形式化陈述：mk_of_mem_addSubgroup [AddGroup Y] (f : X -> Y) (hf : f in locallyFinsuppW
ithin.addSubgroup U) : locallyFinsuppWithin U Y
参数：f : X -> Y；hf : f in locallyFinsuppWithin.addSubgroup U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assign a function with locally finite support within `U` to a function in the su
bgroup.
-/
def mk_of_mem_addSubgroup [AddGroup Y] (f : X → Y) (hf : f ∈ locallyFinsuppWithin.addSubgroup U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩

@[deprecated (since := "2026-03-06")] alias mk_of_mem := mk_of_mem_addSubgroup
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup Y] : Neg (locallyFinsuppWithin U Y) where
  neg D := mk_of_mem_addSubgroup (-D) <| neg_mem D.memAddSubgroup
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup Y] : Sub (locallyFinsuppWithin U Y) where
  sub D₁ D₂ := mk_of_mem_addSubgroup (D₁ - D₂) <| sub_mem D₁.memAddSubgroup D₂.memAddSubgroup
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup Y] : SMul ℤ (locallyFinsuppWithin U Y) where
  smul n D := mk_of_mem_addSubgroup (n • D) <| zsmul_mem D.memAddSubgroup n
/-
**Function.locallyFinsuppWithin.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.loc
allyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddMonoid Y], ⇑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_zero [AddMonoid Y] :
    ((0 : locallyFinsuppWithin U Y) : X → Y) = 0 := rfl
/-
**Function.locallyFinsuppWithin.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.loca
llyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddMonoid Y]   (D₁ D₂ : Function.locallyFinsuppWithin U Y), ⇑(D₁ + D₂) =
 ⇑D₁ + ⇑D₂
参数：D₁ D₂ : Function.locallyFinsuppWithin U Y；D₁ + D₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_add [AddMonoid Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ + D₂) : X → Y) = D₁ + D₂ := rfl
/-
**Function.locallyFinsuppWithin.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Function.loca
llyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddGroup Y]   (D : Function.locallyFinsuppWithin U Y), ⇑(-D) = -⇑D
参数：D : Function.locallyFinsuppWithin U Y；-D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_neg [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (↑(-D) : X → Y) = -(D : X → Y) := rfl
/-
**Function.locallyFinsuppWithin.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Function.loca
llyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddGroup Y]   (D₁ D₂ : Function.locallyFinsuppWithin U Y), ⇑(D₁ - D₂) = 
⇑D₁ - ⇑D₂
参数：D₁ D₂ : Function.locallyFinsuppWithin U Y；D₁ - D₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_sub [AddGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ - D₂) : X → Y) = D₁ - D₂ := rfl
/-
**Function.locallyFinsuppWithin.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Function.lo
callyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddMonoid Y]   (D : Function.locallyFinsuppWithin U Y) (n : ℕ), ⇑(n • D)
 = n • ⇑D
参数：D : Function.locallyFinsuppWithin U Y；n : ℕ；n • D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_nsmul [AddMonoid Y] (D : locallyFinsuppWithin U Y) (n : ℕ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl
/-
**Function.locallyFinsuppWithin.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Function.lo
callyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddGroup Y]   (D : Function.locallyFinsuppWithin U Y) (n : ℤ), ⇑(n • D) 
= n • ⇑D
参数：D : Function.locallyFinsuppWithin U Y；n : ℤ；n • D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_zsmul [AddGroup Y] (D : locallyFinsuppWithin U Y) (n : ℤ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid Y] : AddMonoid (locallyFinsuppWithin U Y) :=
  Injective.addMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_nsmul
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid Y] : AddCommMonoid (locallyFinsuppWithin U Y) :=
  Injective.addCommMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_nsmul
/-
**Function.locallyFinsuppWithin.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `Function.loca
llyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddCommMonoid Y] {ι : Type u_3}   {s : Finset ι} {F : ι → Function.local
lyFinsuppWithin U Y}, ⇑(∑ n ∈ s, F n) = ∑ n ∈ s, ⇑(F n)
参数：∑ n ∈ s, F n；F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma coe_sum [AddCommMonoid Y] {ι : Type*} {s : Finset ι}
    {F : ι → locallyFinsuppWithin U Y} :
    (↑(∑ n ∈ s, F n) : X → Y) = ∑ n ∈ s, (F n : X → Y) := by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | insert => simp_all
/-
**Function.locallyFinsuppWithin.coe_finsum** 是 Mathlib 中的一个定理，位于命名空间 `Function.l
ocallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {ι : Type u_3} {F
 : ι → Function.locallyFinsuppWithin U ℤ},   ⇑(∑ᶠ (i : ι), F i) = ∑ᶠ (i : ι), ⇑(
F i)
参数：∑ᶠ (i : ι), F i；i : ι；F i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Function.locallyFinsuppWithin.coe_sum`：∀ {X : Type u_1} [inst : Topologi
calSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommMonoid Y] {ι : Type u_3}
   {s : Finset ι} {F : ι → …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finsum_of_infinite_support`：∀ {α : Type u_1} {M : Type u_5} [inst : AddC
ommMonoid M] {f : α → M},   (Function.support f).Infinite → ∑ᶠ (i : α), f i = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
@[simp] lemma coe_finsum {ι : Type*} {F : ι → locallyFinsuppWithin U ℤ} :
    (↑(∑ᶠ i, F i) : X → ℤ) = ∑ᶠ i, (F i : X → ℤ) := by
  have : F.support = (fun i ↦ (F i : X → ℤ)).support := by
    simp [Set.ext_iff, DFunLike.ext_iff, funext_iff]
  by_cases h : F.support.Finite
  · rw [finsum_eq_sum F h, Function.locallyFinsuppWithin.coe_sum]
    have h₂ : (fun i ↦ (F i : X → ℤ)).support.Finite := by simp_all
    simp_all [finsum_eq_sum _ h₂]
  · simp_all [finsum_of_infinite_support]
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup Y] : AddGroup (locallyFinsuppWithin U Y) :=
  Injective.addGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

/--
Simplifier lemma: Support does not change when replacing a function with locally finite support by
its negative.
-/
/-
**Function.locallyFinsuppWithin.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `Function.
locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : AddGroup Y]   (D : Function.locallyFinsuppWithin U Y), (-D).support = D.
support
参数：D : Function.locallyFinsuppWithin U Y；-D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.locallyFinsuppWithin.support.eq_1`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y]   (D : Function.lo
callyFinsuppWithin U Y), D.suppo…
· 使用定理 `Function.locallyFinsuppWithin.coe_neg`：∀ {X : Type u_1} [inst : Topologi
calSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddGroup Y]   (D : Function.loc
allyFinsuppWithin U Y), ⇑(-…
· 使用定理 `Function.support_neg`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f : α → G), Function.support (-f) = Function.support f

--- 原说明 ---
Simplifier lemma: Support does not change when replacing a function with locally
 finite support by
its negative.
-/
@[simp] lemma support_neg [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (-D).support = D.support := by rw [support, coe_neg, Function.support_neg]
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup Y] : AddCommGroup (locallyFinsuppWithin U Y) :=
  Injective.addCommGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE Y] [Zero Y] : LE (locallyFinsuppWithin U Y) where
  le := fun D₁ D₂ ↦ (D₁ : X → Y) ≤ D₂
/-
**Function.locallyFinsuppWithin.le_def** 是 Mathlib 中的一个引理，位于命名空间 `Function.local
lyFinsuppWithin`。
形式化陈述：le_def [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} : D₁ <= D₂ ↔ (D₁
 : X -> Y) <= (D₂ : X -> Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_def [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ ≤ D₂ ↔ (D₁ : X → Y) ≤ (D₂ : X → Y) := ⟨(·),(·)⟩
/-
**Function.locallyFinsuppWithin.single_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：single_nonneg [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} : 0 <=
 single x y ↔ 0 <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.locallyFinsuppWithin.coe_single`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x : X}
 {y : Y},   ⇑(Function.locally…
· 使用定理 `Pi.single_nonneg`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : DecidableE
q ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i : 
ι} {a …
-/
lemma single_nonneg [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} :
    0 ≤ single x y ↔ 0 ≤ y := by
  simp only [le_def, coe_single]
  apply Pi.single_nonneg
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder Y] [Zero Y] : LT (locallyFinsuppWithin U Y) where
  lt := fun D₁ D₂ ↦ (D₁ : X → Y) < D₂
/-
**Function.locallyFinsuppWithin.lt_def** 是 Mathlib 中的一个引理，位于命名空间 `Function.local
lyFinsuppWithin`。
形式化陈述：lt_def [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} : D₁ < D₂ 
↔ (D₁ : X -> Y) < (D₂ : X -> Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_def [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ < D₂ ↔ (D₁ : X → Y) < (D₂ : X → Y) := ⟨(·),(·)⟩
/-
**Function.locallyFinsuppWithin.single_pos** 是 Mathlib 中的一个引理，位于命名空间 `Function.l
ocallyFinsuppWithin`。
形式化陈述：single_pos [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} : 0 < sin
gle x y ↔ 0 < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.lt_def`：lt_def [Preorder Y] [Zero Y] {D₁ D
₂ : locallyFinsuppWithin U Y} : D₁ < D₂ ↔ (D₁ : X -> Y) < (D₂ : X -> Y)
· 使用定理 `Function.locallyFinsuppWithin.coe_single`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x : X}
 {y : Y},   ⇑(Function.locally…
· 使用定理 `Pi.single_pos`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : DecidableEq ι
] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i : ι} 
{a …
-/
lemma single_pos [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} :
    0 < single x y ↔ 0 < y := by
  rw [lt_def, coe_single]
  exact Pi.single_pos
/-
**Function.locallyFinsuppWithin.single_pos_nat_one** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : DecidableEq X] {x :
 X},   0 < Function.locallyFinsuppWithin.single x 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.locallyFinsuppWithin.single_pos`：single_pos [DecidableEq X] [Ze
ro Y] [Preorder Y] {x : X} {y : Y} : 0 < single x y ↔ 0 < y
-/
@[simp] lemma single_pos_nat_one [DecidableEq X] {x : X} :
    0 < single x 1 := single_pos.2 Nat.one_pos
/-
**Function.locallyFinsuppWithin.single_pos_int_one** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : DecidableEq X] {x :
 X},   0 < Function.locallyFinsuppWithin.single x 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.locallyFinsuppWithin.single_pos`：single_pos [DecidableEq X] [Ze
ro Y] [Preorder Y] {x : X} {y : Y} : 0 < single x y ↔ 0 < y
· 使用定理 `Int.one_pos`：0 < 1
-/
@[simp] lemma single_pos_int_one [DecidableEq X] {x : X} :
    0 < single x (1 : ℤ) := single_pos.2 Int.one_pos
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeSup Y] [Zero Y] : Max (locallyFinsuppWithin U Y) where
  max D₁ D₂ :=
  { toFun z := max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      obtain ⟨t₁, ht₁⟩ := D₁.supportLocallyFiniteWithinDomain z hz
      obtain ⟨t₂, ht₂⟩ := D₂.supportLocallyFiniteWithinDomain z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ D₁.support) ∪ (t₂ ∩ D₂.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [mem_inter_iff, mem_support, ne_eq, mem_union, true_and]
      by_contra! hCon
      simp_all }

@[simp]
/-
**Function.locallyFinsuppWithin.max_apply** 是 Mathlib 中的一个引理，位于命名空间 `Function.lo
callyFinsuppWithin`。
形式化陈述：max_apply [SemilatticeSup Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {
x : X} : max D₁ D₂ x = max (D₁ x) (D₂ x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma max_apply [SemilatticeSup Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeInf Y] [Zero Y] : Min (locallyFinsuppWithin U Y) where
  min D₁ D₂ :=
  { toFun z := min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      obtain ⟨t₁, ht₁⟩ := D₁.supportLocallyFiniteWithinDomain z hz
      obtain ⟨t₂, ht₂⟩ := D₂.supportLocallyFiniteWithinDomain z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ D₁.support) ∪ (t₂ ∩ D₂.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [mem_inter_iff, mem_support, ne_eq, mem_union, true_and]
      by_contra! hCon
      simp_all }

@[simp]
/-
**Function.locallyFinsuppWithin.min_apply** 是 Mathlib 中的一个引理，位于命名空间 `Function.lo
callyFinsuppWithin`。
形式化陈述：min_apply [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {
x : X} : min D₁ D₂ x = min (D₁ x) (D₂ x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_apply [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

section Lattice
variable [Lattice Y]

/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero Y] : Lattice (locallyFinsuppWithin U Y) where
  le_refl := by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x ↦ (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x ↦ by simp
  le_sup_right D₁ D₂ := fun x ↦ by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]
  inf := min
  inf_le_left D₁ D₂ := fun x ↦ by simp
  inf_le_right D₁ D₂ := fun x ↦ by simp
  le_inf D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]

variable [AddCommGroup Y]
/-
**Function.locallyFinsuppWithin.posPart_apply** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : Lattice Y] [inst_2 : AddCommGroup Y]   (a : Function.locallyFinsuppWithi
n U Y) (x : X), a⁺ x = (a x)⁺
参数：a : Function.locallyFinsuppWithin U Y；x : X；a x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma posPart_apply (a : locallyFinsuppWithin U Y) (x : X) : a⁺ x = (a x)⁺ := rfl
/-
**Function.locallyFinsuppWithin.negPart_apply** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [i
nst_1 : Lattice Y] [inst_2 : AddCommGroup Y]   (a : Function.locallyFinsuppWithi
n U Y) (x : X), a⁻ x = (a x)⁻
参数：a : Function.locallyFinsuppWithin U Y；x : X；a x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma negPart_apply (a : locallyFinsuppWithin U Y) (x : X) : a⁻ x = (a x)⁻ := rfl

end Lattice

section LinearOrder
variable [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]

/--
Functions with locally finite support within `U` form an ordered commutative group.
-/
/-
**Function.locallyFinsuppWithin.** 是 Mathlib 中的一个实例，位于命名空间 `Function.locallyFins
uppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functions with locally finite support within `U` form an ordered commutative gro
up.
-/
instance : IsOrderedAddMonoid (locallyFinsuppWithin U Y) where
  add_le_add_left := fun _ _ _ _ ↦ by simpa [le_def]

/--
The positive part of a sum is less than or equal to the sum of the positive parts.
-/
/-
**Function.locallyFinsuppWithin.posPart_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.
locallyFinsuppWithin`。
形式化陈述：posPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) : (f₁ + f₂)⁺ <= f₁
⁺ + f₂⁺
参数：f₁ f₂ : Function.locallyFinsuppWithin U Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `posPart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid 
α] (a : α), a⁺ = a ⊔ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
The positive part of a sum is less than or equal to the sum of the positive part
s.
-/
theorem posPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁺ ≤ f₁⁺ + f₂⁺ := by
  repeat rw [posPart_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

/--
The negative part of a sum is less than or equal to the sum of the negative parts.
-/
/-
**Function.locallyFinsuppWithin.negPart_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.
locallyFinsuppWithin`。
形式化陈述：negPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) : (f₁ + f₂)⁻ <= f₁
⁻ + f₂⁻
参数：f₁ f₂ : Function.locallyFinsuppWithin U Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `negPart_def`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid 
α] (a : α), a⁻ = -a ⊔ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
The negative part of a sum is less than or equal to the sum of the negative part
s.
-/
theorem negPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁻ ≤ f₁⁻ + f₂⁻ := by
  repeat rw [negPart_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_comm, add_le_add]
  · simp [add_nonneg]

/--
Taking the positive part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
@[simp]
/-
**Function.locallyFinsuppWithin.nsmul_posPart** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：nsmul_posPart (n : Nat) (f : locallyFinsuppWithin U Y) : (n • f)⁺ = n • f⁺
参数：n : Nat；f : locallyFinsuppWithin U Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a
 < b → max a b = b
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `nsmul_nonneg`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preorder M
] [AddLeftMono M] {a : M}, 0 ≤ a → ∀ (n : ℕ), 0 ≤ n • a

--- 原说明 ---
Taking the positive part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
theorem nsmul_posPart (n : ℕ) (f : locallyFinsuppWithin U Y) : (n • f)⁺ = n • f⁺ := by
  ext x
  simp only [posPart, max_apply, coe_nsmul, Pi.smul_apply, coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Taking the negative part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
@[simp]
/-
**Function.locallyFinsuppWithin.nsmul_negPart** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：nsmul_negPart (n : Nat) (f : locallyFinsuppWithin U Y) : (n • f)⁻ = n • f⁻
参数：n : Nat；f : locallyFinsuppWithin U Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a
 < b → max a b = b
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `nsmul_nonneg`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preorder M
] [AddLeftMono M] {a : M}, 0 ≤ a → ∀ (n : ℕ), 0 ≤ n • a

--- 原说明 ---
Taking the negative part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
theorem nsmul_negPart (n : ℕ) (f : locallyFinsuppWithin U Y) : (n • f)⁻ = n • f⁻ := by
  ext x
  simp only [negPart, max_apply, coe_neg, coe_nsmul, Pi.neg_apply, Pi.smul_apply, coe_zero,
    Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Every positive function with locally finite supports dominates a singleton indicator.
-/
/-
**Function.locallyFinsuppWithin.exists_single_le_pos** 是 Mathlib 中的一个引理，位于命名空间 `
Function.locallyFinsuppWithin`。
形式化陈述：exists_single_le_pos [DecidableEq X] {D : locallyFinsupp X Int} (h : 0 < D
) : exists e, single e 1 <= D
参数：h : 0 < D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.locallyFinsuppWithin.ext_iff`：∀ {X : Type u_1} [inst : Topologi
calSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y]   {D₁ D₂ : Function.loc
allyFinsuppWithin U Y}, D₁ …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.lt_iff_le_and_ne`：∀ {a b : ℤ}, a < b ↔ a ≤ b ∧ a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
Every positive function with locally finite supports dominates a singleton indic
ator.
-/
lemma exists_single_le_pos [DecidableEq X] {D : locallyFinsupp X ℤ} (h : 0 < D) :
    ∃ e, single e 1 ≤ D := by
  obtain ⟨z, hz⟩ : ∃ z, D z ≠ 0 := by simpa [D.ext_iff] using! (ne_of_lt h).symm
  refine ⟨z, fun e ↦ ?_⟩
  obtain (rfl | he) := eq_or_ne e z
  · simpa [single_apply] using! Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_apply] using! h.le e

end LinearOrder

/-!
## Restriction
-/

/--
If `V` is a subset of `U`, then functions with locally finite support within `U` restrict to
functions with locally finite support within `V`, by setting their values to zero outside of `V`.
-/
/-
**Function.locallyFinsuppWithin.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Function.loc
allyFinsuppWithin`。
形式化陈述：restrict [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subset
eq U) : locallyFinsuppWithin V Y where toFun
参数：D : locallyFinsuppWithin U Y；h : V subseteq U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` is a subset of `U`, then functions with locally finite support within `U`
 restrict to
functions with locally finite support within `V`, by setting their values to zer
o outside of `V`.
-/
noncomputable def restrict [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    locallyFinsuppWithin V Y where
  toFun := by
    classical
    exact fun z ↦ if hz : z ∈ V then D z else 0
  supportWithinDomain' := by
    intro x hx
    simp_rw [dite_eq_ite, mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    exact hx.1
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht⟩ := D.supportLocallyFiniteWithinDomain z (h hz)
    use t, ht.1
    apply Set.Finite.subset (s := t ∩ D.support) ht.2
    intro _ _
    simp_all

open scoped Classical in
/-
**Function.locallyFinsuppWithin.restrict_apply** 是 Mathlib 中的一个引理，位于命名空间 `Functi
on.locallyFinsuppWithin`。
形式化陈述：restrict_apply [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V 
subseteq U) (z : X) : (D.restrict h) z = if z in V then D z else 0
参数：D : locallyFinsuppWithin U Y；h : V subseteq U；z : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_apply [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) (z : X) :
    (D.restrict h) z = if z ∈ V then D z else 0 := rfl
/-
**Function.locallyFinsuppWithin.restrict_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：restrict_eqOn [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V s
ubseteq U) : Set.EqOn (D.restrict h) D V
参数：D : locallyFinsuppWithin U Y；h : V subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_eqOn [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) D V := by
  intro _ _
  simp_all [restrict_apply]
/-
**Function.locallyFinsuppWithin.restrict_eqOn_compl** 是 Mathlib 中的一个引理，位于命名空间 `F
unction.locallyFinsuppWithin`。
形式化陈述：restrict_eqOn_compl [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h
 : V subseteq U) : Set.EqOn (D.restrict h) 0 Vᶜ
参数：D : locallyFinsuppWithin U Y；h : V subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_eqOn_compl [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) 0 Vᶜ := by
  intro _ hx
  simp_all

/--
Restriction of the zero function is the zero function.
-/
/-
**Function.locallyFinsuppWithin.restrict_zero** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {Y : Type u_2} [inst_1 : Zero
 Y] {U V : Set X} (hV : V ⊆ U),   Function.locallyFinsuppWithin.restrict 0 hV = 
0
参数：hV : V ⊆ U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.restrict_apply`：restrict_apply [Zero Y] {V
 : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) (z : X) : (D.restric
t h) z = if z in V then D z else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
Restriction of the zero function is the zero function.
-/
@[simp] lemma restrict_zero [Zero Y] {U V : Set X} (hV : V ⊆ U) :
    restrict (0 : Function.locallyFinsuppWithin U Y) hV = 0 := by
  ext
  rw [restrict_apply]
  aesop

/-- Restriction as a group morphism -/
/-
**Function.locallyFinsuppWithin.restrictMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Fun
ction.locallyFinsuppWithin`。
形式化陈述：restrictMonoidHom [AddCommGroup Y] {V : Set X} (h : V subseteq U) : locall
yFinsuppWithin U Y ->+ locallyFinsuppWithin V Y where toFun D
参数：h : V subseteq U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction as a group morphism
-/
noncomputable def restrictMonoidHom [AddCommGroup Y] {V : Set X} (h : V ⊆ U) :
    locallyFinsuppWithin U Y →+ locallyFinsuppWithin V Y where
  toFun D := D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict_apply, hx]

@[simp]
/-
**Function.locallyFinsuppWithin.restrictMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空
间 `Function.locallyFinsuppWithin`。
形式化陈述：restrictMonoidHom_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWi
thin U Y) (h : V subseteq U) : restrictMonoidHom h D = D.restrict h
参数：D : locallyFinsuppWithin U Y；h : V subseteq U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictMonoidHom_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y)
    (h : V ⊆ U) :
    restrictMonoidHom h D = D.restrict h := by rfl

/--
Present a function with with finite support as a finsum of singleton indicator functions.
-/
/-
**Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self** 是 Mathlib 中的一个定理
，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {Y : Type u_2} [inst_1 : Deci
dableEq X] [inst_2 : AddCommMonoid Y]   {U : Set X} {F : Function.locallyFinsupp
Within U Y},   F.support.Finite →     ∑ᶠ (x : X), Function.locallyFinsuppWithin.
restrict (Function.locallyFinsuppWithin.single x (F x)) ⋯ = F
参数：x : X；Function.locallyFinsuppWithin.single x (F x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.locallyFinsuppWithin.restrict.congr_simp`：∀ {X : Type u_1} [ins
t : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y] {V : Set X}
   (D D_1 : Function.locallyFinsuppWith…
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Function.locallyFinsuppWithin.single_zero`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x : X
},   Function.locallyFinsuppWit…
· 使用定理 `Function.locallyFinsuppWithin.restrict_zero`：∀ {X : Type u_1} [inst : To
pologicalSpace X] {Y : Type u_2} [inst_1 : Zero Y] {U V : Set X} (hV : V ⊆ U),  
 Function.locallyFinsuppWithin.re…
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.locallyFinsuppWithin.coe_sum`：∀ {X : Type u_1} [inst : Topologi
calSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommMonoid Y] {ι : Type u_3}
   {s : Finset ι} {F : ι → …
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `Finset.sum_ite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι) (f g : ι → M),   (∑ x ∈ 
s, if p th…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
Present a function with with finite support as a finsum of singleton indicator f
unctions.
-/
@[simp] lemma sum_apply_smul_single_eq_self [DecidableEq X] [AddCommMonoid Y] {U : Set X}
    {F : Function.locallyFinsuppWithin U Y} (h : F.support.Finite) :
    ∑ᶠ x, ((single x (F x)).restrict (subset_univ U)) = F := by
  have : (fun x ↦ (single x (F x)).restrict (subset_univ U)).support ⊆ h.toFinset := by
    intro
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp [restrict_apply]
  by_cases hz : z ∈ F.support
  · aesop
  · aesop

/--
Represent a function (of locally finite support) that in fact has finite support as a `finsum` of
singleton indicator functions.
-/
/-
**Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ** 是 Mathli
b 中的一个定理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : DecidableEq X] {D :
 Function.locallyFinsupp X ℤ}   (h : (Function.locallyFinsuppWithin.support D).F
inite),   ∑ z ∈ h.toFinset, Function.locallyFinsuppWithin.single z (D z) = D
参数：h : (Function.locallyFinsuppWithin.support D).Finite；D z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.locallyFinsuppWithin.coe_sum`：∀ {X : Type u_1} [inst : Topologi
calSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommMonoid Y] {ι : Type u_3}
   {s : Finset ι} {F : ι → …
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0

--- 原说明 ---
Represent a function (of locally finite support) that in fact has finite support
 as a `finsum` of
singleton indicator functions.
-/
@[simp] lemma sum_apply_smul_single_eq_self_on_univ [DecidableEq X] {D : locallyFinsupp X ℤ}
    (h : D.support.Finite) :
    ∑ z ∈ h.toFinset, single z (D z) = D := by
  ext w
  simp only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
  set s := h.toFinset with hs
  by_cases hw : w ∈ s
  · simp [hw]
  · simp only [hw, if_false]
    have : w ∉ support D := by simpa only [hs, Set.Finite.mem_toFinset] using hw
    exact (notMem_support.mp this).symm

/-- Restriction as a lattice morphism -/
/-
**Function.locallyFinsuppWithin.restrictLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Fu
nction.locallyFinsuppWithin`。
形式化陈述：restrictLatticeHom [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V subsete
q U) : LatticeHom (locallyFinsuppWithin U Y) (locallyFinsuppWithin V Y) where to
Fun D
参数：h : V subseteq U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction as a lattice morphism
-/
noncomputable def restrictLatticeHom [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V ⊆ U) :
    LatticeHom (locallyFinsuppWithin U Y) (locallyFinsuppWithin V Y) where
  toFun D := D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]

@[simp]
/-
**Function.locallyFinsuppWithin.restrictLatticeHom_apply** 是 Mathlib 中的一个引理，位于命名
空间 `Function.locallyFinsuppWithin`。
形式化陈述：restrictLatticeHom_apply [AddCommGroup Y] [Lattice Y] {V : Set X} (D : loc
allyFinsuppWithin U Y) (h : V subseteq U) : restrictLatticeHom h D = D.restrict 
h
参数：D : locallyFinsuppWithin U Y；h : V subseteq U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictLatticeHom_apply [AddCommGroup Y] [Lattice Y] {V : Set X}
    (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    restrictLatticeHom h D = D.restrict h := by rfl
/--
Restriction commutes with taking positive parts.
-/
/-
**Function.locallyFinsuppWithin.restrict_posPart** 是 Mathlib 中的一个引理，位于命名空间 `Func
tion.locallyFinsuppWithin`。
形式化陈述：restrict_posPart {V : Set X} (D : locallyFinsuppWithin U Int) (h : V subse
teq U) : D⁺.restrict h = (D.restrict h)⁺
参数：D : locallyFinsuppWithin U Int；h : V subseteq U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
Restriction commutes with taking positive parts.
-/
lemma restrict_posPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁺.restrict h = (D.restrict h)⁺ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

/--
Restriction commutes with taking negative parts.
-/
/-
**Function.locallyFinsuppWithin.restrict_negPart** 是 Mathlib 中的一个引理，位于命名空间 `Func
tion.locallyFinsuppWithin`。
形式化陈述：restrict_negPart {V : Set X} (D : locallyFinsuppWithin U Int) (h : V subse
teq U) : D⁻.restrict h = (D.restrict h)⁻
参数：D : locallyFinsuppWithin U Int；h : V subseteq U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
Restriction commutes with taking negative parts.
-/
lemma restrict_negPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁻.restrict h = (D.restrict h)⁻ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop
/-
**Function.locallyFinsuppWithin.disjoint_nhdsWithin_cofinite_of_mem** 是 Mathlib 
中的一个引理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：disjoint_nhdsWithin_cofinite_of_mem [Zero Y] (f : locallyFinsuppWithin U Y
) (p : X) (hp : p in U) : Disjoint (𝓝[f.support] p) cofinite
参数：f : locallyFinsuppWithin U Y；p : X；hp : p in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.disjoint_cofinite_right`：disjoint_cofinite_right : Disjoint l cof
inite ↔ exists s in l, Set.Finite s
· 使用引理 `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain`：supportL
ocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : forall z in U
, exists t in 𝓝 z, Set.Finite (t inter D.support)
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
-/
lemma disjoint_nhdsWithin_cofinite_of_mem [Zero Y]
    (f : locallyFinsuppWithin U Y) (p : X) (hp : p ∈ U) :
    Disjoint (𝓝[f.support] p) cofinite := by
  rw [disjoint_cofinite_right]
  obtain ⟨t, h₁t, h₂t⟩ := f.supportLocallyFiniteWithinDomain p hp
  refine ⟨t ∩ f.support, ?_, h₂t⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  grind
/-
**Function.locallyFinsuppWithin._root_.Function.locallyFinsupp.disjoint_nhdsWith
in_cofinite** 是 Mathlib 中的一个引理，位于命名空间 `Function.locallyFinsuppWithin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.locallyFinsupp.disjoint_nhdsWithin_cofinite
    [Zero Y] (f : locallyFinsupp X Y) (p : X) :
    Disjoint (𝓝[f.support] p) cofinite :=
  disjoint_nhdsWithin_cofinite_of_mem f p (mem_univ _)

end Function.locallyFinsuppWithin

