/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor

/-!

# Pushing a quiver structure along a map

Given a map `σ : V → W` and a `Quiver` instance on `V`, this file defines a `Quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/

@[expose] public section

namespace Quiver

universe v v₁ v₂ u u₁ u₂

variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)

/-- The `Quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unusedArguments]
/-
**Quiver.Push** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：Push (_ : V -> W)
参数：_ : V -> W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W
`
-/
def Push (_ : V → W) :=
  W
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
/-
**Quiver.PushQuiver** 是 Mathlib 中的一个归纳类型，位于命名空间 `Quiver`。
形式化陈述：{V : Type u} → [Quiver V] → {W : Type u₂} → (V → W) → W → W → Type (max u 
u₂ v)
参数：V → W；max u u₂ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W`
-/
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

/-- The prefunctor induced by pushing arrows via `σ` -/
/-
**Quiver.Push.of** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Push`。
形式化陈述：of : V ⥤q Push σ where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prefunctor induced by pushing arrows via `σ`
-/
def of : V ⥤q Push σ where
  obj := σ
  map f := PushQuiver.arrow f

@[simp]
/-
**Quiver.Push.of_obj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Push`。
形式化陈述：of_obj : (of σ).obj = σ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_obj : (of σ).obj = σ :=
  rfl

variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

/-- Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ` to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, where `W` is given
the pushforward quiver structure `Push σ`. -/
/-
**Quiver.Push.lift** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Push`。
形式化陈述：lift : Push σ ⥤q W' where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ`
 to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, whe
re `W` is given
the pushforward quiver structure `Push σ`.
-/
noncomputable def lift : Push σ ⥤q W' where
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      rw [← h X, ← h Y]
      exact φ.map f
/-
**Quiver.Push.lift_obj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Push`。
形式化陈述：lift_obj : (lift σ φ τ h).obj = τ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Quiver.Push.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Push`。
形式化陈述：lift_comp : (of σ ⋙q lift σ φ τ h) = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.ext`：ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{
v₂} W] {F G : Prefunctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : for
all …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prefunctor.comp_obj`：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [
inst_1 : Quiver V] {W : Type u_3} [inst_2 : Quiver W] (F : U ⥤q V)   (G : V ⥤q W
) (X : U)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prefunctor.comp_map`：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [
inst_1 : Quiver V] {W : Type u_3} [inst_2 : Quiver W] (F : U ⥤q V)   (G : V ⥤q W
) {X Y : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `cast_heq`：∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp : (of σ ⋙q lift σ φ τ h) = φ := by
  fapply Prefunctor.ext
  · rintro X
    simp only [Prefunctor.comp_obj]
    apply Eq.symm
    exact h X
  · rintro X Y f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    simp
/-
**Quiver.Push.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Push`。
形式化陈述：lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) 
: Φ = lift σ φ τ h
参数：Φ : Push σ ⥤q W'；Φ₀ : Φ.obj = τ；Φcomp : (of σ ⋙q Φ) = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.ext`：ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{
v₂} W] {F G : Prefunctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : for
all …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr.congr_simp`：∀ {α β : Sort u} (h : α = β) (b b_1 : β), b = b_1 → h
.mpr b = h.mpr b_1
· 使用定理 `Prefunctor.comp_map`：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [
inst_1 : Quiver V] {W : Type u_3} [inst_2 : Quiver W] (F : U ⥤q V)   (G : V ⥤q W
) {X Y : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map]
    rfl

end Push

end Quiver

