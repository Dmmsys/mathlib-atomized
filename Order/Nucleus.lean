/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Mathlib.Order.Closure
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Nucleus

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

A nucleus is an endomorphism of a frame which corresponds to a sublocale.

## References
https://ncatlab.org/nlab/show/sublocale
https://ncatlab.org/nlab/show/nucleus
-/

@[expose] public section

open Order InfHom Set

variable {X : Type*}

/-- A nucleus is an inflationary idempotent `inf`-preserving endomorphism of a semilattice.

In a frame, nuclei correspond to sublocales. See `nucleusIsoSublocale`. -/
/-
**Nucleus** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_2) → [SemilatticeInf X] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nucleus is an inflationary idempotent `inf`-preserving endomorphism of a semil
attice.

In a frame, nuclei correspond to sublocales. See `nucleusIsoSublocale`.
-/
structure Nucleus (X : Type*) [SemilatticeInf X] extends InfHom X X where
  /-- A nucleus is idempotent.

  Do not use this directly. Instead use `NucleusClass.idempotent`. -/
  idempotent' (x : X) : toFun (toFun x) ≤ toFun x
  /-- A nucleus is increasing.

  Do not use this directly. Instead use `NucleusClass.le_apply`. -/
  le_apply' (x : X) : x ≤ toFun x

/-- `NucleusClass F X` states that F is a type of nuclei. -/
/-
**NucleusClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_2) → (X : Type u_3) → [SemilatticeInf X] → [FunLike F X X] → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NucleusClass F X` states that F is a type of nuclei.
-/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] : Prop
    extends InfHomClass F X X where
  /-- A nucleus is idempotent. -/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A nucleus is inflationary. -/
  le_apply (x : X) (f : F) : x ≤ f x

namespace Nucleus
section SemilatticeInf
variable [SemilatticeInf X] {n m : Nucleus X} {x y : X}

/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Nucleus X) X X where
  coe x := x.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

/-- See Note [custom simps projection] -/
/-
**Nucleus.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `Nucleus.Simps`。
形式化陈述：{X : Type u_1} → [inst : SemilatticeInf X] → Nucleus X → X → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (n : Nucleus X) : X → X := n
/-
**Nucleus.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (n : Nucleus X), n.toFun = ⇑n
参数：n : Nucleus X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFun_eq_coe (n : Nucleus X) : n.toFun = n := rfl
/-
**Nucleus.coe_toInfHom** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (n : Nucleus X), ⇑n.toInfHom = 
⇑n
参数：n : Nucleus X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toInfHom (n : Nucleus X) : ⇑n.toInfHom = n := rfl
/-
**Nucleus.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (f : InfHom X X) (h1 : ∀ (x : X
), f.toFun (f.toFun x) ≤ f.toFun x)   (h2 : ∀ (x : X), x ≤ f.toFun x), ⇑{ toInfH
om := f, idempotent' := h1, le_apply' := h2 } = ⇑f
参数：f : InfHom X X；h1 : ∀ (x : X), f.toFun (f.toFun x) ≤ f.toFun x；h2 : ∀ (x : X)
, x ≤ f.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : InfHom X X) (h1 h2) : ⇑(mk f h1 h2) = f := rfl

initialize_simps_projections Nucleus (toFun → apply)
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NucleusClass (Nucleus X) X where
  idempotent _ _ := idempotent' ..
  le_apply _ _ := le_apply' ..
  map_inf _ _ _ := map_inf' ..

/-- Every nucleus is a `ClosureOperator`. -/
/-
**Nucleus.toClosureOperator** 是 Mathlib 中的一个定义，位于命名空间 `Nucleus`。
形式化陈述：toClosureOperator (n : Nucleus X) : ClosureOperator X
参数：n : Nucleus X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nucleus.le_apply'`：∀ {X : Type u_2} [inst : SemilatticeInf X] (self : Nu
cleus X) (x : X), x ≤ self.toFun x
· 使用定理 `Nucleus.idempotent'`：∀ {X : Type u_2} [inst : SemilatticeInf X] (self : 
Nucleus X) (x : X), self.toFun (self.toFun x) ≤ self.toFun x

--- 原说明 ---
Every nucleus is a `ClosureOperator`.
-/
def toClosureOperator (n : Nucleus X) : ClosureOperator X :=
  ClosureOperator.mk' n (OrderHomClass.mono n) n.le_apply' n.idempotent'
/-
**Nucleus.idempotent** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] {n : Nucleus X} (x : X), n (n x
) = n x
参数：x : X；n x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
@[simp] lemma idempotent (x : X) : n (n x) = n x := n.toClosureOperator.idempotent x
/-
**Nucleus.le_apply** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：le_apply : x <= n x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
lemma le_apply : x ≤ n x :=
  n.toClosureOperator.le_closure x
/-
**Nucleus.monotone** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：monotone : Monotone n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
lemma monotone : Monotone n := n.toClosureOperator.monotone
/-
**Nucleus.map_inf** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：map_inf : n (x ⊓ y) = n x ⊓ n y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `NucleusClass.toInfHomClass`：∀ {F : Type u_2} {X : Type u_3} {inst : Semi
latticeInf X} {inst_1 : FunLike F X X} [self : NucleusClass F X],   InfHomClass 
F X X
· 使用定理 `Nucleus.instNucleusClass`：∀ {X : Type u_1} [inst : SemilatticeInf X], Nu
cleusClass (Nucleus X) X
-/
lemma map_inf : n (x ⊓ y) = n x ⊓ n y :=
  InfHomClass.map_inf n x y
/-
**Nucleus.ext** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] {m n : Nucleus X}, (∀ (a : X), 
m a = n a) → m = n
参数：∀ (a : X), m a = n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext {m n : Nucleus X} (h : ∀ a, m a = n a) : m = n :=
  DFunLike.ext m n h
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Nucleus X) := .lift (⇑) DFunLike.coe_injective
/-
**Nucleus.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] {n m : Nucleus X}, ⇑m ≤ ⇑n ↔ m 
≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_le_coe : ⇑m ≤ n ↔ m ≤ n := .rfl
/-
**Nucleus.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] {n m : Nucleus X}, ⇑m < ⇑n ↔ m 
< n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_lt_coe : ⇑m < n ↔ m < n := .rfl
/-
**Nucleus.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (toInfHom₁ toInfHom₂ : InfHom X
 X)   (le_apply₁ : ∀ (x : X), toInfHom₁.toFun (toInfHom₁.toFun x) ≤ toInfHom₁.to
Fun x)   (le_apply₂ : ∀ (x : X), toInfHom₂.toFun (toInfHom₂.toFun x) ≤ toInfHom₂
.toFun x)   (idempotent₁ : ∀ (x : X), x ≤ toInfHom₁.toFun x) (idempotent₂ : ∀ (x
 : X), x ≤ toInfHom₂.toFun x),   { toInfHom := toInfHom₁, idempotent' := le_appl
y₁, le_apply' := idempotent₁ } ≤       { toInfHom := toInfHom₂, idempotent' := l
e_apply₂, le_apply' := idempotent₂ } ↔     toInfHom₁ ≤ toInfHom₂
参数：toInfHom₁ toInfHom₂ : InfHom X X；le_apply₁ : ∀ (x : X), toInfHom₁.toFun (toIn
fHom₁.toFun x) ≤ toInfHom₁.toFun x；le_apply₂ : ∀ (x : X), toInfHom₂.toFun (toInf
Hom₂.toFun x) ≤ toInfHom₂.toFun x；idempotent₁ : ∀ (x : X), x ≤ toInfHom₁.toFun x
；idempotent₂ : ∀ (x : X), x ≤ toInfHom₂.toFun x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, gcongr] lemma mk_le_mk (toInfHom₁ toInfHom₂ : InfHom X X)
    (le_apply₁ le_apply₂ idempotent₁ idempotent₂) :
    mk toInfHom₁ le_apply₁ idempotent₁ ≤ mk toInfHom₂ le_apply₂ idempotent₂ ↔
      toInfHom₁ ≤ toInfHom₂ := .rfl
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Nucleus X) where
  min m n := {
    toFun := m ⊓ n
    map_inf' x y := by simp [inf_inf_inf_comm]
    idempotent' x := by
      simp only [Pi.inf_apply, map_inf, idempotent]
      exact inf_le_inf inf_le_left inf_le_right
    le_apply' x := le_inf m.le_apply n.le_apply
  }
/-
**Nucleus.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (m n : Nucleus X), ⇑(m ⊓ n) = ⇑
m ⊓ ⇑n
参数：m n : Nucleus X；m ⊓ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (m n : Nucleus X) : ⇑(m ⊓ n) = ⇑m ⊓ ⇑n := rfl
/-
**Nucleus.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (m n : Nucleus X) (x : X), (m ⊓
 n) x = m x ⊓ n x
参数：m n : Nucleus X；x : X；m ⊓ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inf_apply (m n : Nucleus X) (x : X) : (m ⊓ n) x = m x ⊓ n x := rfl
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (Nucleus X) :=
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

/-- The smallest nucleus is the identity. -/
/-
**Nucleus.instBot** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
形式化陈述：instBot : OrderBot (Nucleus X) where bot.toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest nucleus is the identity.
-/
instance instBot : OrderBot (Nucleus X) where
  bot.toFun x := x
  bot.idempotent' := by simp
  bot.le_apply' := by simp
  bot.map_inf' := by simp
  bot_le n _ := n.le_apply
/-
**Nucleus.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X], ⇑⊥ = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : Nucleus X) = id := rfl
/-
**Nucleus.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] (x : X), ⊥ x = x
参数：x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma bot_apply (x : X) : (⊥ : Nucleus X) x = x := rfl

variable [OrderTop X]

/-- A nucleus preserves `⊤`. -/
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nucleus preserves `⊤`.
-/
instance : TopHomClass (Nucleus X) X X where
  map_top _ := eq_top_iff.mpr le_apply

/-- The largest nucleus sends everything to `⊤`. -/
/-
**Nucleus.instTop** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
形式化陈述：instTop : Top (Nucleus X) where top.toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest nucleus sends everything to `⊤`.
-/
instance instTop : Top (Nucleus X) where
  top.toFun := ⊤
  top.idempotent' := by simp
  top.le_apply' := by simp
  top.map_inf' := by simp
/-
**Nucleus.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] [inst_1 : OrderTop X], ⇑⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : ⇑(⊤ : Nucleus X) = ⊤ := rfl
/-
**Nucleus.top_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : SemilatticeInf X] [inst_1 : OrderTop X] (x : X), 
⊤ x = ⊤
参数：x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_apply (x : X) : (⊤ : Nucleus X) x = ⊤ := rfl
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (Nucleus X) where
  bot_le _ _ := le_apply
  le_top _ _ := by simp

end SemilatticeInf

section CompleteLattice
variable [CompleteLattice X]

/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Nucleus X) where
  sInf s :=
  { toFun x := ⨅ f ∈ s, f x,
    map_inf' x y := by
      simp only [InfHomClass.map_inf, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro f hf
      · exact iInf₂_le_of_le f hf inf_le_left
      · exact iInf₂_le_of_le f hf inf_le_right
      · exact ⟨inf_le_of_left_le <| iInf₂_le f hf, inf_le_of_right_le <| iInf₂_le f hf⟩
    idempotent' x := iInf₂_mono fun f hf ↦ (f.monotone <| iInf₂_le f hf).trans_eq (f.idempotent _)
    le_apply' x := by simp [le_apply] }
/-
**Nucleus.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : CompleteLattice X] (s : Set (Nucleus X)) (x : X),
 (sInf s) x = ⨅ j ∈ s, j x
参数：s : Set (Nucleus X)；x : X；sInf s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sInf_apply (s : Set (Nucleus X)) (x : X) : sInf s x = ⨅ j ∈ s, j x := rfl
/-
**Nucleus.iInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : CompleteLattice X] {ι : Type u_2} (f : ι → Nucleu
s X) (x : X), (iInf f) x = ⨅ j, (f j) x
参数：f : ι → Nucleus X；x : X；iInf f；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Nucleus.sInf_apply`：∀ {X : Type u_1} [inst : CompleteLattice X] (s : Set
 (Nucleus X)) (x : X), (sInf s) x = ⨅ j ∈ s, j x
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
@[simp] lemma iInf_apply {ι : Type*} (f : ι → (Nucleus X)) (x : X) : iInf f x = ⨅ j, f j x := by
  rw [iInf, sInf_apply, iInf_range]
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeInf (Nucleus X) where
  isGLB_sInf _ :=
    ⟨by simp +contextual [mem_lowerBounds, ← coe_le_coe, Pi.le_def, iInf_le_iff],
      by simp +contextual [mem_lowerBounds, mem_upperBounds, ← coe_le_coe, Pi.le_def]⟩
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Nucleus X) where
  __ : SemilatticeInf (Nucleus X) := inferInstance
  __ : OrderBot (Nucleus X) := inferInstance
  __ : OrderTop (Nucleus X) := inferInstance
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus X)

end CompleteLattice

section Frame
variable [Order.Frame X] {n m : Nucleus X} {x y : X}

/-
**Nucleus.map_himp_le** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：map_himp_le : n (x ⇨ y) <= x ⇨ n y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Nucleus.le_apply`：le_apply : x <= n x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nucleus.map_inf`：map_inf : n (x ⊓ y) = n x ⊓ n y
· 使用定理 `himp_inf_self`：himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `NucleusClass.toInfHomClass`：∀ {F : Type u_2} {X : Type u_3} {inst : Semi
latticeInf X} {inst_1 : FunLike F X X} [self : NucleusClass F X],   InfHomClass 
F X X
· 使用定理 `Nucleus.instNucleusClass`：∀ {X : Type u_1} [inst : SemilatticeInf X], Nu
cleusClass (Nucleus X) X
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma map_himp_le : n (x ⇨ y) ≤ x ⇨ n y := by
  rw [le_himp_iff]
  calc
    n (x ⇨ y) ⊓ x
    _ ≤ n (x ⇨ y) ⊓ n x := by gcongr; exact n.le_apply
    _ = n (y ⊓ x) := by rw [← map_inf, himp_inf_self]
    _ ≤ n y := by gcongr; exact inf_le_left
/-
**Nucleus.map_himp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：map_himp_apply (n : Nucleus X) (x y : X) : n (x ⇨ n y) = x ⇨ n y
参数：n : Nucleus X；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Nucleus.map_himp_le`：map_himp_le : n (x ⇨ y) <= x ⇨ n y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nucleus.idempotent`：∀ {X : Type u_1} [inst : SemilatticeInf X] {n : Nucl
eus X} (x : X), n (n x) = n x
· 使用引理 `Nucleus.le_apply`：le_apply : x <= n x
-/
lemma map_himp_apply (n : Nucleus X) (x y : X) : n (x ⇨ n y) = x ⇨ n y :=
  le_antisymm (map_himp_le.trans_eq <| by rw [n.idempotent]) n.le_apply
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HImp (Nucleus X) where
  himp m n :=
  { toFun x := ⨅ y ≥ x, m y ⇨ n y
    idempotent' x := le_iInf₂ fun y hy ↦
      calc
        ⨅ z ≥ ⨅ w ≥ x, m w ⇨ n w, m z ⇨ n z
        _ ≤ m (m y ⇨ n y) ⇨ n (m y ⇨ n y) := iInf₂_le (m y ⇨ n y) <| iInf₂_le y hy
        _ = m y ⇨ n y := by
          rw [map_himp_apply, himp_himp, ← map_inf, inf_of_le_right (le_trans n.le_apply le_himp)]
    map_inf' x y := by
      simp only [and_assoc, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨fun z hxz ↦ iInf₂_le _ <| inf_le_of_left_le hxz,
        fun z hyz ↦ iInf₂_le _ <| inf_le_of_right_le hyz, ?_⟩
      have : Nonempty X := ⟨x⟩
      simp only [iInf_inf, le_iInf_iff, le_himp_iff, iInf_le_iff, le_inf_iff, forall_and,
        forall_const, and_imp]
      intro k hxyk l hlx hly hlk
      calc
        l = (l ⊓ m (x ⊔ k)) ⊓ (l ⊓ m (y ⊔ k)) := by
          rw [← inf_inf_distrib_left, ← map_inf, ← sup_inf_right, sup_eq_right.2 hxyk,
            inf_eq_left.2 hlk]
        _ ≤ n (x ⊔ k) ⊓ n (y ⊔ k) := by
          gcongr; exacts [hlx (x ⊔ k) le_sup_left, hly (y ⊔ k) le_sup_left]
        _ = n k := by rw [← map_inf, ← sup_inf_right, sup_eq_right.2 hxyk]
    le_apply' := by
      simpa using fun _ _ h ↦ inf_le_of_left_le <| h.trans n.le_apply }
/-
**Nucleus.himp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] (m n : Nucleus X) (x : X), (m ⇨ n)
 x = ⨅ y, ⨅ (_ : y ≥ x), m y ⇨ n y
参数：m n : Nucleus X；x : X；m ⇨ n；_ : y ≥ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma himp_apply (m n : Nucleus X) (x : X) : (m ⇨ n) x = ⨅ y ≥ x, m y ⇨ n y := rfl
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HeytingAlgebra (Nucleus X) where
  compl m := m ⇨ ⊥
  le_himp_iff _ n _ := by
    simpa [← coe_le_coe, Pi.le_def]
      using ⟨fun h i ↦ h i i le_rfl, fun h i j _ ↦ (h j).trans' <| by gcongr⟩
  himp_bot m := rfl
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Order.Frame (Nucleus X) where
  __ := Nucleus.instHeytingAlgebra
  __ := Nucleus.instCompleteLattice
/-
**Nucleus.mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：mem_range : x in range n ↔ n x = x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nucleus.idempotent`：∀ {X : Type u_1} [inst : SemilatticeInf X] {n : Nucl
eus X} (x : X), n (n x) = n x
-/
lemma mem_range : x ∈ range n ↔ n x = x where
  mp := by rintro ⟨x, rfl⟩; exact idempotent _
  mpr h := ⟨x, h⟩

set_option backward.privateInPublic true in
/-- See `Nucleus.giRestrict` for the public-facing version. -/
/-
**Nucleus.giAux** 是 Mathlib 中的一个定义，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Nucleus.giRestrict` for the public-facing version.
-/
private def giAux (n : Nucleus X) : GaloisInsertion (rangeFactorization n) Subtype.val where
  choice x hx := ⟨x, mem_range.2 <| hx.antisymm n.le_apply⟩
  gc x y := ClosureOperator.IsClosed.closure_le_iff (c := n.toClosureOperator) <| mem_range.1 y.2
  le_l_u x := le_apply
  choice_eq x hx := by ext; exact le_apply.antisymm hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (range n) := n.giAux.liftCompleteLattice
/-
**Nucleus.** 是 Mathlib 中的一个实例，位于命名空间 `Nucleus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Frame (range n) := .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s := by
    simp_rw [← Subtype.coe_le_coe, iSup_subtype', iSup, sSup, n.giAux.gc.u_inf]
    rw [rangeFactorization_coe, ← mem_range.1 a.prop, ← map_inf]
    apply n.monotone
    simp_rw [inf_sSup_eq, sSup_image, iSup_range, iSup_image, iSup_subtype', n.giAux.gc.u_inf,
      le_rfl] }

/-- Restrict a nucleus to its range. -/
/-
**Nucleus.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Nucleus`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → (n : Nucleus X) → FrameHom X ↑(S
et.range ⇑n)
参数：n : Nucleus X；Set.range ⇑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a nucleus to its range.
-/
@[simps] def restrict (n : Nucleus X) : FrameHom X (range n) where
  toFun := rangeFactorization n
  map_inf' a b := by ext; exact map_inf
  map_top' := by ext; exact map_top n
  map_sSup' s := by rw [n.giAux.gc.l_sSup, sSup_image]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The restriction of a nucleus to its range forms a Galois insertion with the forgetful map from
the range to the original frame. -/
/-
**Nucleus.giRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Nucleus`。
形式化陈述：giRestrict (n : Nucleus X) : GaloisInsertion n.restrict Subtype.val
参数：n : Nucleus X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a nucleus to its range forms a Galois insertion with the forg
etful map from
the range to the original frame.
-/
def giRestrict (n : Nucleus X) : GaloisInsertion n.restrict Subtype.val := n.giAux
/-
**Nucleus.comp_eq_right_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：comp_eq_right_iff_le : n ∘ m = m ↔ n <= m where mpr h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nucleus.coe_le_coe`：∀ {X : Type u_1} [inst : SemilatticeInf X] {n m : Nu
cleus X}, ⇑m ≤ ⇑n ↔ m ≤ n
· 使用引理 `Nucleus.monotone`：monotone : Monotone n
· 使用引理 `Nucleus.le_apply`：le_apply : x <= n x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nucleus.idempotent'`：∀ {X : Type u_2} [inst : SemilatticeInf X] (self : 
Nucleus X) (x : X), self.toFun (self.toFun x) ≤ self.toFun x
-/
lemma comp_eq_right_iff_le : n ∘ m = m ↔ n ≤ m where
  mpr h := funext_iff.mpr <| fun _ ↦ le_antisymm (le_trans (h (m _)) (m.idempotent' _)) le_apply
  mp h := by
    rw [← coe_le_coe, ← h]
    exact fun _ ↦ monotone le_apply
/-
**Nucleus.range_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {n m : Nucleus X}, Set.range ⇑m ⊆ 
Set.range ⇑n ↔ n ≤ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nucleus.mem_range`：mem_range : x in range n ↔ n x = x where mp
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用引理 `Nucleus.monotone`：monotone : Monotone n
· 使用引理 `Nucleus.le_apply`：le_apply : x <= n x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_range_iff_exists_comp`：range_subset_range_iff_exists_co
mp {f : α -> γ} {g : β -> γ} : range f subseteq range g ↔ exists h : α -> β, f =
 g ∘ h
· 使用引理 `Nucleus.comp_eq_right_iff_le`：comp_eq_right_iff_le : n ∘ m = m ↔ n <= m 
where mpr h
-/
@[simp] lemma range_subset_range : range m ⊆ range n ↔ n ≤ m where
  mp h x := by
    rw [← mem_range.mp (Set.range_subset_iff.mp h x)]
    exact n.monotone m.le_apply
  mpr h :=
    range_subset_range_iff_exists_comp.mpr ⟨m, (comp_eq_right_iff_le.mpr h).symm⟩

end Frame
end Nucleus

