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

/--
Definition of `Nucleus` / `Nucleus` 的定义

English:
structure Nucleus
  parameters: (X : Type*) [SemilatticeInf X]
  extends: InfHom X X
  axioms and operations (2):
    - idempotent'((x : X)) : toFun (toFun x) <= toFun x
    - le_apply'((x : X)) : x <= toFun x

中文:
结构 Nucleus
  参数: (X : 类型) [SemilatticeInf X]
  继承: InfHom X X
  公理与运算 (2 个):
    - idempotent'((x : X)) : toFun (toFun x) <= toFun x
    - le_apply'((x : X)) : x <= toFun x
-/
structure Nucleus (X : Type*) [SemilatticeInf X] extends InfHom X X where
  /-- A nucleus is idempotent.

  Do not use this directly. Instead use `NucleusClass.idempotent`. -/
  idempotent' (x : X) : toFun (toFun x) <= toFun x
  /-- A nucleus is increasing.

  Do not use this directly. Instead use `NucleusClass.le_apply`. -/
  le_apply' (x : X) : x <= toFun x

/--
Definition of `NucleusClass` / `NucleusClass` 的定义

English:
class NucleusClass
  parameters: (F X : Type*) [SemilatticeInf X] [FunLike F X X]
  extends: InfHomClass F X X
  axioms and operations (2):
    - idempotent((x : X) (f : F)) : f (f x) <= f x
    - le_apply((x : X) (f : F)) : x <= f x

中文:
类 NucleusClass
  参数: (F X : 类型) [SemilatticeInf X] [FunLike F X X]
  继承: InfHomClass F X X
  公理与运算 (2 个):
    - idempotent((x : X) (f : F)) : f (f x) <= f x
    - le_apply((x : X) (f : F)) : x <= f x
-/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] : Prop
    extends InfHomClass F X X where
  /-- A nucleus is idempotent. -/
  idempotent (x : X) (f : F) : f (f x) <= f x
  /-- A nucleus is inflationary. -/
  le_apply (x : X) (f : F) : x <= f x

namespace Nucleus
section SemilatticeInf
variable [SemilatticeInf X] {n m : Nucleus X} {x y : X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Nucleus X) X X
  body: x.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

中文:
实例 :
  签名: FunLike (Nucleus X) X X
  定义体: x.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

Depends on / 依赖: x.toFun
-/
instance : FunLike (Nucleus X) X X where
  coe x := x.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (n : Nucleus X)
  body: n

中文:
定义 Simps.apply
  签名: (n : Nucleus X)
  定义体: n
-/
def Simps.apply (n : Nucleus X) : X -> X := n

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (n : Nucleus X)
  statement: n.toFun = n
  proof: rfl

中文:
引理 toFun_eq_coe
  条件: (n : Nucleus X)
  结论: n.toFun = n
  证明: rfl
-/
@[simp] lemma toFun_eq_coe (n : Nucleus X) : n.toFun = n := rfl
/--
lemma `coe_toInfHom` / 引理 `coe_toInfHom`

English:
lemma coe_toInfHom
  given: (n : Nucleus X)
  statement: ⇑n.toInfHom = n
  proof: rfl

中文:
引理 coe_toInfHom
  条件: (n : Nucleus X)
  结论: ⇑n.toInfHom = n
  证明: rfl
-/
@[simp] lemma coe_toInfHom (n : Nucleus X) : ⇑n.toInfHom = n := rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : InfHom X X) (h1 h2)
  statement: ⇑(mk f h1 h2) = f
  proof: rfl

initialize_simps_projections Nucleus (toFun -> apply)

中文:
引理 coe_mk
  条件: (f : InfHom X X) (h1 h2)
  结论: ⇑(mk f h1 h2) = f
  证明: rfl

initialize_simps_projections Nucleus (toFun -> apply)
-/
@[simp] lemma coe_mk (f : InfHom X X) (h1 h2) : ⇑(mk f h1 h2) = f := rfl

initialize_simps_projections Nucleus (toFun -> apply)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NucleusClass (Nucleus X) X
  body: idempotent' ..
  le_apply _ _ := le_apply' ..
  map_inf _ _ _ := map_inf' ..

中文:
实例 :
  签名: NucleusClass (Nucleus X) X
  定义体: idempotent' ..
  le_apply _ _ := le_apply' ..
  map_inf _ _ _ := map_inf' ..

Depends on / 依赖: idempotent
-/
instance : NucleusClass (Nucleus X) X where
  idempotent _ _ := idempotent' ..
  le_apply _ _ := le_apply' ..
  map_inf _ _ _ := map_inf' ..

/--
Definition of `toClosureOperator` / `toClosureOperator` 的定义

English:
definition toClosureOperator
  signature: (n : Nucleus X)
  body: ClosureOperator.mk' n (OrderHomClass.mono n) n.le_apply' n.idempotent'

中文:
定义 toClosureOperator
  签名: (n : Nucleus X)
  定义体: ClosureOperator.mk' n (OrderHomClass.mono n) n.le_apply' n.idempotent'

Depends on / 依赖: ClosureOperator, ClosureOperator.mk, OrderHomClass, OrderHomClass.mono, idempotent, le_apply, n.idempotent, n.le_apply
-/
def toClosureOperator (n : Nucleus X) : ClosureOperator X :=
  ClosureOperator.mk' n (OrderHomClass.mono n) n.le_apply' n.idempotent'

/--
lemma `idempotent` / 引理 `idempotent`

English:
lemma idempotent
  given: (x : X)
  statement: n (n x) = n x
  proof: n.toClosureOperator.idempotent x

中文:
引理 idempotent
  条件: (x : X)
  结论: n (n x) = n x
  证明: n.toClosureOperator.idempotent x
-/
@[simp] lemma idempotent (x : X) : n (n x) = n x := n.toClosureOperator.idempotent x

/--
lemma `le_apply` / 引理 `le_apply`

English:
lemma le_apply
  statement: x <= n x
  proof: n.toClosureOperator.le_closure x

中文:
引理 le_apply
  结论: x <= n x
  证明: n.toClosureOperator.le_closure x

Depends on / 依赖: le_closure, n.toClosureOperator.le_closure, toClosureOperator
-/
lemma le_apply : x <= n x :=
  n.toClosureOperator.le_closure x

/--
lemma `monotone` / 引理 `monotone`

English:
lemma monotone
  statement: Monotone n
  proof: n.toClosureOperator.monotone

中文:
引理 monotone
  结论: Monotone n
  证明: n.toClosureOperator.monotone

Depends on / 依赖: monotone, n.toClosureOperator.monotone, toClosureOperator
-/
lemma monotone : Monotone n := n.toClosureOperator.monotone

/--
lemma `map_inf` / 引理 `map_inf`

English:
lemma map_inf
  statement: n (x ⊓ y) = n x ⊓ n y
  proof: InfHomClass.map_inf n x y

中文:
引理 map_inf
  结论: n (x ⊓ y) = n x ⊓ n y
  证明: InfHomClass.map_inf n x y

Depends on / 依赖: InfHomClass, InfHomClass.map_inf, map_inf
-/
lemma map_inf : n (x ⊓ y) = n x ⊓ n y :=
  InfHomClass.map_inf n x y

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {m n : Nucleus X} (h : forall a, m a = n a)
  statement: m = n
  proof: DFunLike.ext m n h

中文:
引理 ext
  条件: {m n : Nucleus X} (h : 对任意 a, m a = n a)
  结论: m = n
  证明: DFunLike.ext m n h
-/
@[ext] lemma ext {m n : Nucleus X} (h : forall a, m a = n a) : m = n :=
  DFunLike.ext m n h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Nucleus X)
  body: .lift (⇑) DFunLike.coe_injective

中文:
实例 :
  签名: PartialOrder (Nucleus X)
  定义体: .lift (⇑) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
instance : PartialOrder (Nucleus X) := .lift (⇑) DFunLike.coe_injective

/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: ⇑m <= n ↔ m <= n
  proof: .rfl

中文:
引理 coe_le_coe
  结论: ⇑m <= n ↔ m <= n
  证明: .rfl
-/
@[simp, norm_cast] lemma coe_le_coe : ⇑m <= n ↔ m <= n := .rfl
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: ⇑m < n ↔ m < n
  proof: .rfl

中文:
引理 coe_lt_coe
  结论: ⇑m < n ↔ m < n
  证明: .rfl
-/
@[simp, norm_cast] lemma coe_lt_coe : ⇑m < n ↔ m < n := .rfl

/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  statement: (toInfHom₁ toInfHom₂ : InfHom X X)
  proof: .rfl

中文:
引理 mk_le_mk
  结论: (toInfHom₁ toInfHom₂ : InfHom X X)
  证明: .rfl
-/
@[simp, gcongr] lemma mk_le_mk (toInfHom₁ toInfHom₂ : InfHom X X)
    (le_apply₁ le_apply₂ idempotent₁ idempotent₂) :
    mk toInfHom₁ le_apply₁ idempotent₁ <= mk toInfHom₂ le_apply₂ idempotent₂ ↔
      toInfHom₁ <= toInfHom₂ := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Nucleus X)
  body: {
    toFun := m ⊓ n
    map_inf' x y := by simp [inf_inf_inf_comm]
    idempotent' x := by
      simp only [Pi.inf_apply, map_inf, idempotent]
      exact inf_le_inf inf_le_left inf_le_right
    le_apply' x := le_inf m.le_apply n.le_apply
  }

中文:
实例 :
  签名: Min (Nucleus X)
  定义体: {
    toFun := m ⊓ n
    map_inf' x y := by simp [inf_inf_inf_comm]
    idempotent' x := by
      simp only [Pi.inf_apply, map_inf, idempotent]
      exact inf_le_inf inf_le_left inf_le_right
    le_apply' x := le_inf m.le_apply n.le_apply
  }
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

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (m n : Nucleus X)
  statement: ⇑(m ⊓ n) = ⇑m ⊓ ⇑n
  proof: rfl

中文:
引理 coe_inf
  条件: (m n : Nucleus X)
  结论: ⇑(m ⊓ n) = ⇑m ⊓ ⇑n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (m n : Nucleus X) : ⇑(m ⊓ n) = ⇑m ⊓ ⇑n := rfl
/--
lemma `inf_apply` / 引理 `inf_apply`

English:
lemma inf_apply
  given: (m n : Nucleus X) (x : X)
  statement: (m ⊓ n) x = m x ⊓ n x
  proof: rfl

中文:
引理 inf_apply
  条件: (m n : Nucleus X) (x : X)
  结论: (m ⊓ n) x = m x ⊓ n x
  证明: rfl
-/
@[simp] lemma inf_apply (m n : Nucleus X) (x : X) : (m ⊓ n) x = m x ⊓ n x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (Nucleus X)
  body: DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

中文:
实例 :
  签名: SemilatticeInf (Nucleus X)
  定义体: DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeInf, coe_inf, coe_injective, semilatticeInf
-/
instance : SemilatticeInf (Nucleus X) :=
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : OrderBot (Nucleus X) where
  body: x
  bot.idempotent' := by simp
  bot.le_apply' := by simp
  bot.map_inf' := by simp
  bot_le n _ := n.le_apply

中文:
实例 instBot
  签名: : OrderBot (Nucleus X) where
  定义体: x
  bot.idempotent' := by simp
  bot.le_apply' := by simp
  bot.map_inf' := by simp
  bot_le n _ := n.le_apply
-/
instance instBot : OrderBot (Nucleus X) where
  bot.toFun x := x
  bot.idempotent' := by simp
  bot.le_apply' := by simp
  bot.map_inf' := by simp
  bot_le n _ := n.le_apply

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ⇑(⊥ : Nucleus X) = id
  proof: rfl

中文:
引理 coe_bot
  结论: ⇑(⊥ : Nucleus X) = id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : Nucleus X) = id := rfl
/--
lemma `bot_apply` / 引理 `bot_apply`

English:
lemma bot_apply
  given: (x : X)
  statement: (⊥ : Nucleus X) x = x
  proof: rfl

中文:
引理 bot_apply
  条件: (x : X)
  结论: (⊥ : Nucleus X) x = x
  证明: rfl
-/
@[simp] lemma bot_apply (x : X) : (⊥ : Nucleus X) x = x := rfl

variable [OrderTop X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopHomClass (Nucleus X) X X
  body: eq_top_iff.mpr le_apply

中文:
实例 :
  签名: TopHomClass (Nucleus X) X X
  定义体: eq_top_iff.mpr le_apply

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, le_apply
-/
instance : TopHomClass (Nucleus X) X X where
  map_top _ := eq_top_iff.mpr le_apply

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (Nucleus X) where
  body: ⊤
  top.idempotent' := by simp
  top.le_apply' := by simp
  top.map_inf' := by simp

中文:
实例 instTop
  签名: : Top (Nucleus X) where
  定义体: ⊤
  top.idempotent' := by simp
  top.le_apply' := by simp
  top.map_inf' := by simp
-/
instance instTop : Top (Nucleus X) where
  top.toFun := ⊤
  top.idempotent' := by simp
  top.le_apply' := by simp
  top.map_inf' := by simp

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ⇑(⊤ : Nucleus X) = ⊤
  proof: rfl

中文:
引理 coe_top
  结论: ⇑(⊤ : Nucleus X) = ⊤
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : ⇑(⊤ : Nucleus X) = ⊤ := rfl
/--
lemma `top_apply` / 引理 `top_apply`

English:
lemma top_apply
  given: (x : X)
  statement: (⊤ : Nucleus X) x = ⊤
  proof: rfl

中文:
引理 top_apply
  条件: (x : X)
  结论: (⊤ : Nucleus X) x = ⊤
  证明: rfl
-/
@[simp] lemma top_apply (x : X) : (⊤ : Nucleus X) x = ⊤ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (Nucleus X)
  body: le_apply
  le_top _ _ := by simp

中文:
实例 :
  签名: BoundedOrder (Nucleus X)
  定义体: le_apply
  le_top _ _ := by simp

Depends on / 依赖: le_apply
-/
instance : BoundedOrder (Nucleus X) where
  bot_le _ _ := le_apply
  le_top _ _ := by simp

end SemilatticeInf

section CompleteLattice
variable [CompleteLattice X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Nucleus X)
  body: { toFun x := ⨅ f in s, f x,
    map_inf' x y := by
      simp only [InfHomClass.map_inf, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro f hf
      · exact iInf₂_le_of_le f hf inf_le_left
      · exact iInf₂_le_of_le f hf inf_le_right
· exact ⟨inf_le_of_left_le iInf₂

中文:
实例 :
  签名: InfSet (Nucleus X)
  定义体: { toFun x := ⨅ f in s, f x,
    map_inf' x y := by
      simp only [InfHomClass.map_inf, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro f hf
      · exact iInf₂_le_of_le f hf inf_le_left
      · exact iInf₂_le_of_le f hf inf_le_right
· exact ⟨inf_le_of_left_le iInf₂

Depends on / 依赖: InfHomClass, InfHomClass.map_inf, f.idempotent, f.monotone, idempotent, inf_le_left, inf_le_of_left_le, inf_le_of_right_le, inf_le_right, le_antisymm_iff, le_apply, le_iInf_iff, le_inf_iff, map_inf, monotone, trans_eq
-/
instance : InfSet (Nucleus X) where
  sInf s :=
  { toFun x := ⨅ f in s, f x,
    map_inf' x y := by
      simp only [InfHomClass.map_inf, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro f hf
      · exact iInf₂_le_of_le f hf inf_le_left
      · exact iInf₂_le_of_le f hf inf_le_right
· exact ⟨inf_le_of_left_le iInf₂_le f hf, inf_le_of_right_le iInf₂_le f hf⟩
    idempotent' x := iInf₂_mono fun f hf => (f.monotone <| iInf₂_le f hf).trans_eq (f.idempotent _)
    le_apply' x := by simp [le_apply] }

/--
lemma `sInf_apply` / 引理 `sInf_apply`

English:
lemma sInf_apply
  given: (s : Set (Nucleus X)) (x : X)
  statement: sInf s x = ⨅ j in s, j x
  proof: rfl

中文:
引理 sInf_apply
  条件: (s : Set (Nucleus X)) (x : X)
  结论: sInf s x = ⨅ j in s, j x
  证明: rfl
-/
@[simp] lemma sInf_apply (s : Set (Nucleus X)) (x : X) : sInf s x = ⨅ j in s, j x := rfl

/--
lemma `iInf_apply` / 引理 `iInf_apply`

English:
lemma iInf_apply
  given: {ι : Type*} (f : ι -> (Nucleus X)) (x : X)
  statement: iInf f x = ⨅ j, f j x
  proof: by
  rw [iInf]; rw [sInf_apply]; rw [iInf_range]

中文:
引理 iInf_apply
  条件: {ι : 类型} (f : ι -> (Nucleus X)) (x : X)
  结论: iInf f x = ⨅ j, f j x
  证明: by
  rw [iInf]; rw [sInf_apply]; rw [iInf_range]
-/
@[simp] lemma iInf_apply {ι : Type*} (f : ι -> (Nucleus X)) (x : X) : iInf f x = ⨅ j, f j x := by
  rw [iInf]; rw [sInf_apply]; rw [iInf_range]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (Nucleus X)
  body: ⟨by simp +contextual [mem_lowerBounds, ← coe_le_coe, Pi.le_def, iInf_le_iff],
      by simp +contextual [mem_lowerBounds, mem_upperBounds, ← coe_le_coe, Pi.le_def]⟩

中文:
实例 :
  签名: CompleteSemilatticeInf (Nucleus X)
  定义体: ⟨by simp +contextual [mem_lowerBounds, ← coe_le_coe, Pi.le_def, iInf_le_iff],
      by simp +contextual [mem_lowerBounds, mem_upperBounds, ← coe_le_coe, Pi.le_def]⟩

Depends on / 依赖: Pi.le_def, coe_le_coe, contextual, iInf_le_iff, le_def, mem_lowerBounds, mem_upperBounds
-/
instance : CompleteSemilatticeInf (Nucleus X) where
  isGLB_sInf _ :=
    ⟨by simp +contextual [mem_lowerBounds, ← coe_le_coe, Pi.le_def, iInf_le_iff],
      by simp +contextual [mem_lowerBounds, mem_upperBounds, ← coe_le_coe, Pi.le_def]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Nucleus X)
  body: inferInstance
  __ : OrderBot (Nucleus X) := inferInstance
  __ : OrderTop (Nucleus X) := inferInstance
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus X)

中文:
实例 :
  签名: CompleteLattice (Nucleus X)
  定义体: inferInstance
  __ : OrderBot (Nucleus X) := inferInstance
  __ : OrderTop (Nucleus X) := inferInstance
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus X)
-/
instance : CompleteLattice (Nucleus X) where
  __ : SemilatticeInf (Nucleus X) := inferInstance
  __ : OrderBot (Nucleus X) := inferInstance
  __ : OrderTop (Nucleus X) := inferInstance
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus X)

end CompleteLattice

section Frame
variable [Order.Frame X] {n m : Nucleus X} {x y : X}

/--
lemma `map_himp_le` / 引理 `map_himp_le`

English:
lemma map_himp_le
  statement: n (x ⇨ y) <= x ⇨ n y
  proof: by
  rw [le_himp_iff]
  calc
    n (x ⇨ y) ⊓ x
    _ <= n (x ⇨ y) ⊓ n x := by gcongr; exact n.le_apply
    _ = n (y ⊓ x) := by rw [← map_inf, himp_inf_self]
    _ <= n y := by gcongr; exact inf_le_left

中文:
引理 map_himp_le
  结论: n (x ⇨ y) <= x ⇨ n y
  证明: by
  rw [le_himp_iff]
  calc
    n (x ⇨ y) ⊓ x
    _ <= n (x ⇨ y) ⊓ n x := by gcongr; exact n.le_apply
    _ = n (y ⊓ x) := by rw [← map_inf, himp_inf_self]
    _ <= n y := by gcongr; exact inf_le_left

Depends on / 依赖: himp_inf_self, inf_le_left, le_apply, le_himp_iff, map_inf, n.le_apply
-/
lemma map_himp_le : n (x ⇨ y) <= x ⇨ n y := by
  rw [le_himp_iff]
  calc
    n (x ⇨ y) ⊓ x
    _ <= n (x ⇨ y) ⊓ n x := by gcongr; exact n.le_apply
    _ = n (y ⊓ x) := by rw [← map_inf, himp_inf_self]
    _ <= n y := by gcongr; exact inf_le_left

/--
lemma `map_himp_apply` / 引理 `map_himp_apply`

English:
lemma map_himp_apply
  given: (n : Nucleus X) (x y : X)
  statement: n (x ⇨ n y) = x ⇨ n y
  proof: le_antisymm (map_himp_le.trans_eq <| by rw [n.idempotent]) n.le_apply

中文:
引理 map_himp_apply
  条件: (n : Nucleus X) (x y : X)
  结论: n (x ⇨ n y) = x ⇨ n y
  证明: le_antisymm (map_himp_le.trans_eq <| by rw [n.idempotent]) n.le_apply

Depends on / 依赖: idempotent, le_antisymm, le_apply, map_himp_le, map_himp_le.trans_eq, n.idempotent, n.le_apply, trans_eq
-/
lemma map_himp_apply (n : Nucleus X) (x y : X) : n (x ⇨ n y) = x ⇨ n y :=
  le_antisymm (map_himp_le.trans_eq <| by rw [n.idempotent]) n.le_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HImp (Nucleus X)
  body: { toFun x := ⨅ y >= x, m y ⇨ n y
    idempotent' x := le_iInf₂ fun y hy =>
      calc
        ⨅ z >= ⨅ w >= x, m w ⇨ n w, m z ⇨ n z
_ <= m (m y ⇨ n y) ⇨ n (m y ⇨ n y) := iInf₂_le (m y ⇨ n y) iInf₂_le y hy
        _ = m y ⇨ n y := by
          rw [map_himp_apply]; rw [himp_himp]; rw [← map_inf]; rw [

中文:
实例 :
  签名: HImp (Nucleus X)
  定义体: { toFun x := ⨅ y >= x, m y ⇨ n y
    idempotent' x := le_iInf₂ fun y hy =>
      calc
        ⨅ z >= ⨅ w >= x, m w ⇨ n w, m z ⇨ n z
_ <= m (m y ⇨ n y) ⇨ n (m y ⇨ n y) := iInf₂_le (m y ⇨ n y) iInf₂_le y hy
        _ = m y ⇨ n y := by
          rw [map_himp_apply]; rw [himp_himp]; rw [← map_inf]; rw [

Depends on / 依赖: and_assoc, himp_himp, idempotent, inf_le_of_left_le, inf_le_of_right_le, inf_of_le_right, le_antisymm_iff, le_apply, le_himp, le_iInf_iff, le_inf_iff, le_trans, map_himp_apply, map_inf, n.le_apply
-/
instance : HImp (Nucleus X) where
  himp m n :=
  { toFun x := ⨅ y >= x, m y ⇨ n y
    idempotent' x := le_iInf₂ fun y hy =>
      calc
        ⨅ z >= ⨅ w >= x, m w ⇨ n w, m z ⇨ n z
_ <= m (m y ⇨ n y) ⇨ n (m y ⇨ n y) := iInf₂_le (m y ⇨ n y) iInf₂_le y hy
        _ = m y ⇨ n y := by
          rw [map_himp_apply]; rw [himp_himp]; rw [← map_inf]; rw [inf_of_le_right (le_trans n.le_apply le_himp)]
    map_inf' x y := by
      simp only [and_assoc, le_antisymm_iff, le_inf_iff, le_iInf_iff]
refine ⟨fun z hxz => iInf₂_le _ inf_le_of_left_le hxz,
fun z hyz => iInf₂_le _ inf_le_of_right_le hyz, ?_⟩
      have : Nonempty X := ⟨x⟩
      simp only [iInf_inf, le_iInf_iff, le_himp_iff, iInf_le_iff, le_inf_iff, forall_and,
        forall_const, and_imp]
      intro k hxyk l hlx hly hlk
      calc
        l = (l ⊓ m (x ⊔ k)) ⊓ (l ⊓ m (y ⊔ k)) := by
          rw [← inf_inf_distrib_left]; rw [← map_inf]; rw [← sup_inf_right]; rw [sup_eq_right.2 hxyk]; rw [inf_eq_left.2 hlk]
        _ <= n (x ⊔ k) ⊓ n (y ⊔ k) := by
          gcongr; exacts [hlx (x ⊔ k) le_sup_left, hly (y ⊔ k) le_sup_left]
        _ = n k := by rw [← map_inf, ← sup_inf_right, sup_eq_right.2 hxyk]
    le_apply' := by
simpa using fun _ _ h => inf_le_of_left_le h.trans n.le_apply }

/--
lemma `himp_apply` / 引理 `himp_apply`

English:
lemma himp_apply
  given: (m n : Nucleus X) (x : X)
  statement: (m ⇨ n) x = ⨅ y >= x, m y ⇨ n y
  proof: rfl

中文:
引理 himp_apply
  条件: (m n : Nucleus X) (x : X)
  结论: (m ⇨ n) x = ⨅ y >= x, m y ⇨ n y
  证明: rfl
-/
@[simp] lemma himp_apply (m n : Nucleus X) (x : X) : (m ⇨ n) x = ⨅ y >= x, m y ⇨ n y := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HeytingAlgebra (Nucleus X)
  body: m ⇨ ⊥
  le_himp_iff _ n _ := by
    simpa [← coe_le_coe, Pi.le_def]
using ⟨fun h i => h i i le_rfl, fun h i j _ => (h j).trans' by gcongr⟩
  himp_bot m := rfl

中文:
实例 :
  签名: HeytingAlgebra (Nucleus X)
  定义体: m ⇨ ⊥
  le_himp_iff _ n _ := by
    simpa [← coe_le_coe, Pi.le_def]
using ⟨fun h i => h i i le_rfl, fun h i j _ => (h j).trans' by gcongr⟩
  himp_bot m := rfl
-/
instance : HeytingAlgebra (Nucleus X) where
  compl m := m ⇨ ⊥
  le_himp_iff _ n _ := by
    simpa [← coe_le_coe, Pi.le_def]
using ⟨fun h i => h i i le_rfl, fun h i j _ => (h j).trans' by gcongr⟩
  himp_bot m := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Order.Frame (Nucleus X)
  body: Nucleus.instHeytingAlgebra
  __ := Nucleus.instCompleteLattice

中文:
实例 :
  签名: Order.Frame (Nucleus X)
  定义体: Nucleus.instHeytingAlgebra
  __ := Nucleus.instCompleteLattice

Depends on / 依赖: Nucleus, Nucleus.instHeytingAlgebra, instHeytingAlgebra
-/
instance : Order.Frame (Nucleus X) where
  __ := Nucleus.instHeytingAlgebra
  __ := Nucleus.instCompleteLattice

/--
lemma `mem_range` / 引理 `mem_range`

English:
lemma mem_range
  statement: x in range n ↔ n x = x where
  proof: by rintro ⟨x, rfl⟩; exact idempotent _
  mpr h := ⟨x, h⟩

中文:
引理 mem_range
  结论: x in range n ↔ n x = x where
  证明: by rintro ⟨x, rfl⟩; exact idempotent _
  mpr h := ⟨x, h⟩

Depends on / 依赖: Algebra, Algebra.IsPushout.isIntegral, IsPushout, idempotent, isIntegral
-/
lemma mem_range : x in range n ↔ n x = x where
  mp := by rintro ⟨x, rfl⟩; exact idempotent _
  mpr h := ⟨x, h⟩

set_option backward.privateInPublic true in
/--
Definition of `giAux` / `giAux` 的定义

English:
definition giAux
  signature: (n : Nucleus X)
  body: ⟨x, mem_range.2 hx.antisymm n.le_apply⟩
gc x y := ClosureOperator.IsClosed.closure_le_iff (c := n.toClosureOperator) mem_range.1 y.2
  le_l_u x := le_apply
  choice_eq x hx := by ext; exact le_apply.antisymm hx

中文:
定义 giAux
  签名: (n : Nucleus X)
  定义体: ⟨x, mem_range.2 hx.antisymm n.le_apply⟩
gc x y := ClosureOperator.IsClosed.closure_le_iff (c := n.toClosureOperator) mem_range.1 y.2
  le_l_u x := le_apply
  choice_eq x hx := by ext; exact le_apply.antisymm hx
-/
private def giAux (n : Nucleus X) : GaloisInsertion (rangeFactorization n) Subtype.val where
choice x hx := ⟨x, mem_range.2 hx.antisymm n.le_apply⟩
gc x y := ClosureOperator.IsClosed.closure_le_iff (c := n.toClosureOperator) mem_range.1 y.2
  le_l_u x := le_apply
  choice_eq x hx := by ext; exact le_apply.antisymm hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (range n)
  body: n.giAux.liftCompleteLattice

中文:
实例 :
  签名: CompleteLattice (range n)
  定义体: n.giAux.liftCompleteLattice

Depends on / 依赖: liftCompleteLattice, n.giAux.liftCompleteLattice
-/
instance : CompleteLattice (range n) := n.giAux.liftCompleteLattice

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Frame (range n)
  body: .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s := by
    simp_rw [← Subtype.coe_le_coe, iSup_subtype', iSup, sSup, n.giAux.gc.u_inf]
    rw [rangeFactorization_coe]; rw [← mem_range.1 a.prop]; rw [← map_inf]
    apply n.monotone
    simp_rw [inf_sSup_eq, sSup_image, iSup_range, iSup_image, iSup_subty

中文:
实例 :
  签名: Frame (range n)
  定义体: .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s := by
    simp_rw [← Subtype.coe_le_coe, iSup_subtype', iSup, sSup, n.giAux.gc.u_inf]
    rw [rangeFactorization_coe]; rw [← mem_range.1 a.prop]; rw [← map_inf]
    apply n.monotone
    simp_rw [inf_sSup_eq, sSup_image, iSup_range, iSup_image, iSup_subty

Depends on / 依赖: ofMinimalAxioms
-/
instance : Frame (range n) := .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s := by
    simp_rw [← Subtype.coe_le_coe, iSup_subtype', iSup, sSup, n.giAux.gc.u_inf]
    rw [rangeFactorization_coe]; rw [← mem_range.1 a.prop]; rw [← map_inf]
    apply n.monotone
    simp_rw [inf_sSup_eq, sSup_image, iSup_range, iSup_image, iSup_subtype', n.giAux.gc.u_inf,
      le_rfl] }

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (n : Nucleus X)
  body: rangeFactorization n
  map_inf' a b := by ext; exact map_inf
  map_top' := by ext; exact map_top n
  map_sSup' s := by rw [n.giAux.gc.l_sSup, sSup_image]

中文:
定义 restrict
  签名: (n : Nucleus X)
  定义体: rangeFactorization n
  map_inf' a b := by ext; exact map_inf
  map_top' := by ext; exact map_top n
  map_sSup' s := by rw [n.giAux.gc.l_sSup, sSup_image]
-/
@[simps] def restrict (n : Nucleus X) : FrameHom X (range n) where
  toFun := rangeFactorization n
  map_inf' a b := by ext; exact map_inf
  map_top' := by ext; exact map_top n
  map_sSup' s := by rw [n.giAux.gc.l_sSup, sSup_image]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `giRestrict` / `giRestrict` 的定义

English:
definition giRestrict
  signature: (n : Nucleus X)
  body: n.giAux

中文:
定义 giRestrict
  签名: (n : Nucleus X)
  定义体: n.giAux

Depends on / 依赖: n.giAux
-/
def giRestrict (n : Nucleus X) : GaloisInsertion n.restrict Subtype.val := n.giAux

/--
lemma `comp_eq_right_iff_le` / 引理 `comp_eq_right_iff_le`

English:
lemma comp_eq_right_iff_le
  statement: n ∘ m = m ↔ n <= m where
  proof: funext_iff.mpr fun _ => le_antisymm (le_trans (h (m _)) (m.idempotent' _)) le_apply
  mp h := by
    rw [← coe_le_coe]; rw [← h]
    exact fun _ => monotone le_apply

中文:
引理 comp_eq_right_iff_le
  结论: n ∘ m = m ↔ n <= m where
  证明: funext_iff.mpr fun _ => le_antisymm (le_trans (h (m _)) (m.idempotent' _)) le_apply
  mp h := by
    rw [← coe_le_coe]; rw [← h]
    exact fun _ => monotone le_apply

Depends on / 依赖: funext_iff, funext_iff.mpr, idempotent, le_antisymm, le_apply, le_trans, m.idempotent
-/
lemma comp_eq_right_iff_le : n ∘ m = m ↔ n <= m where
mpr h := funext_iff.mpr fun _ => le_antisymm (le_trans (h (m _)) (m.idempotent' _)) le_apply
  mp h := by
    rw [← coe_le_coe]; rw [← h]
    exact fun _ => monotone le_apply

/--
lemma `range_subset_range` / 引理 `range_subset_range`

English:
lemma range_subset_range
  statement: range m subseteq range n ↔ n <= m where
  proof: by
    rw [← mem_range.mp (Set.range_subset_iff.mp h x)]
    exact n.monotone m.le_apply
  mpr h :=
    range_subset_range_iff_exists_comp.mpr ⟨m, (comp_eq_right_iff_le.mpr h).symm⟩

中文:
引理 range_subset_range
  结论: range m subseteq range n ↔ n <= m where
  证明: by
    rw [← mem_range.mp (Set.range_subset_iff.mp h x)]
    exact n.monotone m.le_apply
  mpr h :=
    range_subset_range_iff_exists_comp.mpr ⟨m, (comp_eq_right_iff_le.mpr h).symm⟩
-/
@[simp] lemma range_subset_range : range m subseteq range n ↔ n <= m where
  mp h x := by
    rw [← mem_range.mp (Set.range_subset_iff.mp h x)]
    exact n.monotone m.le_apply
  mpr h :=
    range_subset_range_iff_exists_comp.mpr ⟨m, (comp_eq_right_iff_le.mpr h).symm⟩

end Frame
end Nucleus
