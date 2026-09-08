/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.PPWithUniv

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `Shrink α : Type w`, and `equivShrink α : α ≃ Shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `Small.{w} α ↔ Small.{w} β`.

See `Mathlib/Logic/Small/Basic.lean` for further instances and theorems.
-/

@[expose] public section

universe u w v v'

/-- A type is `Small.{w}` if there exists an equivalence to some `S : Type w`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423: `v` is a true output (determined by `α`),
-- but we need the attribute to prevent `w` from also being treated as output.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params v, mk_iff, pp_with_univ]
/-
**Small** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type v → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class Small (α : Type v) : Prop where
  /-- If a type is `Small.{w}`, then there exists an equivalence with some `S : Type w` -/
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)

/-- Constructor for `Small α` from an explicit witness type and equivalence.
-/
/-
**Small.mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α
参数：e : α ≃ S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Small α` from an explicit witness type and equivalence.
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩

/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[pp_with_univ, no_expose]
/-
**Shrink** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Shrink (α : Type v) [Small.{w} α] : Type w
参数：α : Type v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Small.equiv_small`：∀ {α : Type v} [self : Small.{w, v} α], ∃ S, Nonempty
 (α ≃ S)

--- 原说明 ---
An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)

/-- The noncomputable equivalence between a `w`-small type and a model.
-/
@[no_expose]
/-
**equivShrink** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α
参数：α : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))

@[ext]
/-
**Shrink.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Shrink.ext {α : Type v} [Small.{w} α] {x y : Shrink α} (w : (equivShrink _
).symm x = (equivShrink _).symm y) : x = y
参数：w : (equivShrink _).symm x = (equivShrink _).symm y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem Shrink.ext {α : Type v} [Small.{w} α] {x y : Shrink α}
    (w : (equivShrink _).symm x = (equivShrink _).symm y) : x = y := by
  simpa using w

-- It would be nice to mark this as `aesop cases` if
-- https://github.com/leanprover-community/aesop/issues/59
-- is resolved.
@[induction_eliminator]
/-
**Shrink.rec** 是 Mathlib 中的一个定义，位于命名空间 `Shrink`。
形式化陈述：{α : Type u_1} →   [inst : Small.{w, u_1} α] →     {F : Shrink.{w, u_1} α 
→ Sort v} → ((X : α) → F ((equivShrink α) X)) → (X : Shrink.{w, u_1} α) → F X
参数：(X : α) → F ((equivShrink α) X)；X : Shrink.{w, u_1} α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
protected noncomputable def Shrink.rec {α : Type*} [Small.{w} α] {F : Shrink α → Sort v}
    (h : ∀ X, F (equivShrink _ X)) : ∀ X, F X :=
  fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

@[simp]
/-
**Shrink.rec_equivShrink** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Shrink.rec_equivShrink {α : Type*} [Small.{w} α] {F : Shrink α -> Sort v} 
{f : (a : α) -> F (equivShrink α a)} (a : α) : Shrink.rec f (equivShrink _ a) = 
f a
参数：a : α；equivShrink α a；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eqRec_eq_cast`：∀ {α : Sort u_1} {a : α} {motive : (a' : α) → a = a' → So
rt u_2} (x : motive a ⋯) {a' : α} (e : a = a'),   e ▸ x = cast ⋯ x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma Shrink.rec_equivShrink {α : Type*} [Small.{w} α] {F : Shrink α → Sort v}
    {f : (a : α) → F (equivShrink α a)} (a : α) : Shrink.rec f (equivShrink _ a) = f a := by
  simp only [Shrink.rec, eqRec_eq_cast, cast_eq_iff_heq]
  rw [Equiv.symm_apply_apply]
/-
**small_self** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_self (α : Type v) : Small.{v} α
参数：α : Type v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.mk'`：Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
instance small_self (α : Type v) : Small.{v} α :=
  Small.mk' <| Equiv.refl α
/-
**small_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃ β) : Small.{
w} α
参数：e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.equiv_small`：∀ {α : Type v} [self : Small.{w, v} α], ∃ S, Nonempty
 (α ≃ S)
· 使用定理 `Small.mk'`：Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃ β) : Small.{w} α :=
  let ⟨_, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)
/-
**small_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α
参数：α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.mk'`：Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α :=
  let ⟨⟨_, ⟨f⟩⟩⟩ := hα
  Small.mk' <| f.trans (Equiv.ulift.{w}).symm

/-- Due to https://github.com/leanprover/lean4/issues/2297, this is useless as an instance.

See however `Logic.UnivLE`, whose API is able to indirectly provide this instance. -/
/-
**small_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：small_max (α : Type v) : Small.{max w v} α
参数：α : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_lift`：small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w}
 α

--- 原说明 ---
Due to https://github.com/leanprover/lean4/issues/2297, this is useless as an in
stance.

See however `Logic.UnivLE`, whose API is able to indirectly provide this instanc
e.
-/
lemma small_max (α : Type v) : Small.{max w v} α :=
  small_lift.{v, w} α
/-
**small_zero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_zero (α : Type) : Small.{w} α
参数：α : Type。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `small_max`：small_max (α : Type v) : Small.{max w v} α
-/
instance small_zero (α : Type) : Small.{w} α := small_max α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) small_succ (α : Type v) : Small.{v + 1} α :=
  small_lift.{v, v + 1} α
/-
**small_ulift** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α)
参数：α : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
-/
instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α) :=
  small_map Equiv.ulift
/-
**small_plift** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_plift (α : Type u) [Small.{v} α] : Small.{v} (PLift α)
参数：α : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
-/
instance small_plift (α : Type u) [Small.{v} α] : Small.{v} (PLift α) :=
  small_map Equiv.plift
/-
**small_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_type : Small.{max (u + 1) v} (Type u)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `small_max`：small_max (α : Type v) : Small.{max w v} α
-/
theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type u} [Small.{v} α] [Nontrivial α] : Nontrivial (Shrink.{v} α) :=
  (equivShrink α).symm.nontrivial

section

/-
**small_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w} α ↔ Small.{w} 
β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩
/-
**small_sigma** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_sigma {α} (β : α -> Type*) [Small.{w} α] [forall a, Small.{w} (β a)]
 : Small.{w} (Σ a, β a)
参数：β : α -> Type*；β a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Shrink.congr_simp`：∀ (α α_1 : Type v) (e_α : α = α_1) [inst : Small.{w, 
v} α], Shrink.{w, v} α = Shrink.{w, v} α_1
-/
instance small_sigma {α} (β : α → Type*) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (Σ a, β a) :=
  ⟨⟨Σ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**not_small_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：¬Small.{u, max (u + 1) (v + 1)} (Type (max u v))
参数：u + 1；v + 1；Type (max u v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.cantor_injective`：∀ {α : Type u_4} (f : Set α → α), ¬Function.I
njective f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem not_small_type : ¬Small.{u} (Type max u v)
  | ⟨⟨S, ⟨e⟩⟩⟩ =>
    @Function.cantor_injective (Σ α, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩) fun a b e => by
      dsimp at e
      injection e with h₁ h₂
      simpa using h₂

end

