/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Batteries.Logic
public import Mathlib.Init

/-!
# Extra facts about `PProd`
-/

@[expose] public section


open Function

variable {α β γ δ : Sort*}

namespace PProd

/--
Definition of `mk.injArrow` / `mk.injArrow` 的定义

English:
definition mk.injArrow
  signature: {α : Type*} {β : Type*} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  body: by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]

中文:
定义 mk.injArrow
  签名: {α : 类型} {β : 类型} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  定义体: by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]
-/
def mk.injArrow {α : Type*} {β : Type*} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) -> forall ⦃P : Sort*⦄, (x₁ = x₂ -> y₁ = y₂ -> P) -> P := by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]
/--
theorem `mk.eta` / 定理 `mk.eta`

English:
theorem mk.eta
  given: {p : PProd α β}
  statement: PProd.mk p.1 p.2 = p
  proof: rfl

@[simp]

中文:
定理 mk.eta
  条件: {p : 命题积类型 α β}
  结论: 命题积类型.mk p.1 p.2 = p
  证明: rfl

@[simp]
-/
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  rfl

@[simp]
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : PProd α β -> Prop}
  statement: (forall x, p x) ↔ forall a b, p ⟨a, b⟩
  proof: ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]

中文:
定理 «对任意»
  条件: {p : 命题积类型 α β -> 命题}
  结论: (对任意 x, p x) ↔ 对任意 a b, p ⟨a, b⟩
  证明: ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
-/
theorem «forall» {p : PProd α β -> Prop} : (forall x, p x) ↔ forall a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : PProd α β -> Prop}
  statement: (exists x, p x) ↔ exists a b, p ⟨a, b⟩
  proof: ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

中文:
定理 «存在»
  条件: {p : 命题积类型 α β -> 命题}
  结论: (存在 x, p x) ↔ 存在 a b, p ⟨a, b⟩
  证明: ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
-/
theorem «exists» {p : PProd α β -> Prop} : (exists x, p x) ↔ exists a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/--
theorem `forall'` / 定理 `forall'`

English:
theorem forall'
  given: {p : α -> β -> Prop}
  statement: (forall x : PProd α β, p x.1 x.2) ↔ forall a b, p a b
  proof: PProd.forall

中文:
定理 对任意'
  条件: {p : α -> β -> 命题}
  结论: (对任意 x : 命题积类型 α β, p x.1 x.2) ↔ 对任意 a b, p a b
  证明: PProd.forall

Depends on / 依赖: PProd.forall
-/
theorem forall' {p : α -> β -> Prop} : (forall x : PProd α β, p x.1 x.2) ↔ forall a b, p a b :=
  PProd.forall

/--
theorem `exists'` / 定理 `exists'`

English:
theorem exists'
  given: {p : α -> β -> Prop}
  statement: (exists x : PProd α β, p x.1 x.2) ↔ exists a b, p a b
  proof: PProd.exists

中文:
定理 存在'
  条件: {p : α -> β -> 命题}
  结论: (存在 x : 命题积类型 α β, p x.1 x.2) ↔ 存在 a b, p a b
  证明: PProd.exists

Depends on / 依赖: PProd.exists
-/
theorem exists' {p : α -> β -> Prop} : (exists x : PProd α β, p x.1 x.2) ↔ exists a b, p a b :=
  PProd.exists

end PProd

/--
theorem `Function.Injective.pprod_map` / 定理 `Function.Injective.pprod_map`

English:
theorem Function.Injective.pprod_map
  given: {f : α -> β} {g : γ -> δ} (hf : Injective f) (hg : Injective g)
  proof: fun _ _ h =>
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)

中文:
定理 函数.单射.pprod_map
  条件: {f : α -> β} {g : γ -> δ} (hf : 单射 f) (hg : 单射 g)
  证明: fun _ _ h =>
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)
-/
theorem Function.Injective.pprod_map {f : α -> β} {g : γ -> δ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x => ⟨f x.1, g x.2⟩ : PProd α γ -> PProd β δ) := fun _ _ h =>
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)
