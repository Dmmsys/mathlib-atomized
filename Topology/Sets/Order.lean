/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Sets.Closeds

/-!
# Clopen upper sets

In this file we define the type of clopen upper sets.
-/

@[expose] public section


open Set TopologicalSpace

variable {α : Type*} [TopologicalSpace α] [LE α]

/-! ### Compact open sets -/


/--
Definition of `ClopenUpperSet` / `ClopenUpperSet` 的定义

English:
structure ClopenUpperSet
  parameters: (α : Type*) [TopologicalSpace α] [LE α]
  extends: Clopens α
  axioms and operations (1):
    - upper' : IsUpperSet carrier

中文:
结构 既开又闭上集
  参数: (α : 类型) [拓扑空间 α] [LE α]
  继承: Clopens α
  公理与运算 (1 个):
    - upper' : 是上集 carrier
-/
structure ClopenUpperSet (α : Type*) [TopologicalSpace α] [LE α] extends Clopens α where
  upper' : IsUpperSet carrier

namespace ClopenUpperSet

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ClopenUpperSet α) α
  body: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

中文:
实例 :
  签名: 集合状 (既开又闭上集 α) α
  定义体: s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (ClopenUpperSet α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ClopenUpperSet α)
  body: .ofSetLike (ClopenUpperSet α) α

中文:
实例 :
  签名: 偏序 (既开又闭上集 α)
  定义体: .ofSetLike (ClopenUpperSet α) α

Depends on / 依赖: ClopenUpperSet, ofSetLike
-/
instance : PartialOrder (ClopenUpperSet α) := .ofSetLike (ClopenUpperSet α) α

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : ClopenUpperSet α)
  body: s

initialize_simps_projections ClopenUpperSet (carrier -> coe, as_prefix coe)

中文:
定义 Simps.coe
  签名: (s : 既开又闭上集 α)
  定义体: s

initialize_simps_projections ClopenUpperSet (carrier -> coe, as_prefix coe)
-/
def Simps.coe (s : ClopenUpperSet α) : Set α := s

initialize_simps_projections ClopenUpperSet (carrier -> coe, as_prefix coe)

/--
theorem `upper` / 定理 `upper`

English:
theorem upper
  given: (s : ClopenUpperSet α)
  statement: IsUpperSet (s : Set α)
  proof: s.upper'

中文:
定理 upper
  条件: (s : 既开又闭上集 α)
  结论: 是上集 (s : 集合 α)
  证明: s.upper'

Depends on / 依赖: s.upper
-/
theorem upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'

/--
theorem `isClopen` / 定理 `isClopen`

English:
theorem isClopen
  given: (s : ClopenUpperSet α)
  statement: IsClopen (s : Set α)
  proof: s.isClopen'

中文:
定理 isClopen
  条件: (s : 既开又闭上集 α)
  结论: IsClopen (s : 集合 α)
  证明: s.isClopen'

Depends on / 依赖: isClopen, s.isClopen
-/
theorem isClopen (s : ClopenUpperSet α) : IsClopen (s : Set α) :=
  s.isClopen'

/-- Reinterpret an upper clopen as an upper set. -/
@[simps]
/--
Definition of `toUpperSet` / `toUpperSet` 的定义

English:
definition toUpperSet
  signature: (s : ClopenUpperSet α)
  body: ⟨s, s.upper⟩

@[ext]

中文:
定义 toUpperSet
  签名: (s : 既开又闭上集 α)
  定义体: ⟨s, s.upper⟩

@[ext]

Depends on / 依赖: s.upper
-/
def toUpperSet (s : ClopenUpperSet α) : UpperSet α :=
  ⟨s, s.upper⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : ClopenUpperSet α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : 既开又闭上集 α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : ClopenUpperSet α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Clopens α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : Clopens α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl
-/
theorem coe_mk (s : Clopens α) (h) : (mk s h : Set α) = s :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (ClopenUpperSet α)
  body: ⟨fun s t => ⟨s.toClopens ⊔ t.toClopens, s.upper.union t.upper⟩⟩

中文:
实例 :
  签名: 最大值 (既开又闭上集 α)
  定义体: ⟨fun s t => ⟨s.toClopens ⊔ t.toClopens, s.upper.union t.upper⟩⟩

Depends on / 依赖: s.toClopens, s.upper.union, t.toClopens, t.upper, toClopens
-/
instance : Max (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊔ t.toClopens, s.upper.union t.upper⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (ClopenUpperSet α)
  body: ⟨fun s t => ⟨s.toClopens ⊓ t.toClopens, s.upper.inter t.upper⟩⟩

中文:
实例 :
  签名: 最小值 (既开又闭上集 α)
  定义体: ⟨fun s t => ⟨s.toClopens ⊓ t.toClopens, s.upper.inter t.upper⟩⟩

Depends on / 依赖: s.toClopens, s.upper.inter, t.toClopens, t.upper, toClopens
-/
instance : Min (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊓ t.toClopens, s.upper.inter t.upper⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (ClopenUpperSet α)
  body: ⟨⟨⊤, isUpperSet_univ⟩⟩

中文:
实例 :
  签名: 顶元素 (既开又闭上集 α)
  定义体: ⟨⟨⊤, isUpperSet_univ⟩⟩

Depends on / 依赖: isUpperSet_univ
-/
instance : Top (ClopenUpperSet α) :=
  ⟨⟨⊤, isUpperSet_univ⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (ClopenUpperSet α)
  body: ⟨⟨⊥, isUpperSet_empty⟩⟩

中文:
实例 :
  签名: 底元素 (既开又闭上集 α)
  定义体: ⟨⟨⊥, isUpperSet_empty⟩⟩

Depends on / 依赖: isUpperSet_empty
-/
instance : Bot (ClopenUpperSet α) :=
  ⟨⟨⊥, isUpperSet_empty⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (ClopenUpperSet α)
  body: SetLike.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 格 (既开又闭上集 α)
  定义体: SetLike.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: SetLike, SetLike.coe_injective.lattice, coe_injective, lattice
-/
instance : Lattice (ClopenUpperSet α) :=
  SetLike.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (ClopenUpperSet α)
  body: BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl rfl

@[simp]

中文:
实例 :
  签名: 有界序 (既开又闭上集 α)
  定义体: BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl rfl

@[simp]

Depends on / 依赖: BoundedOrder, BoundedOrder.lift
-/
instance : BoundedOrder (ClopenUpperSet α) :=
  BoundedOrder.lift ((↑) : _ -> Set α) (fun _ _ => id) rfl rfl

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : ClopenUpperSet α)
  statement: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  proof: rfl

@[simp]

中文:
定理 coe_sup
  条件: (s t : 既开又闭上集 α)
  结论: (↑(s ⊔ t) : 集合 α) = ↑s union ↑t
  证明: rfl

@[simp]
-/
theorem coe_sup (s t : ClopenUpperSet α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t :=
  rfl

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (s t : ClopenUpperSet α)
  statement: (↑(s ⊓ t) : Set α) = ↑s inter ↑t
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (s t : 既开又闭上集 α)
  结论: (↑(s ⊓ t) : 集合 α) = ↑s inter ↑t
  证明: rfl

@[simp]
-/
theorem coe_inf (s t : ClopenUpperSet α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t :=
  rfl

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: (↑(⊤ : ClopenUpperSet α) : Set α) = univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: (↑(⊤ : 既开又闭上集 α) : 集合 α) = univ
  证明: rfl

@[simp]
-/
theorem coe_top : (↑(⊤ : ClopenUpperSet α) : Set α) = univ :=
  rfl

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: (↑(⊥ : ClopenUpperSet α) : Set α) = ∅
  proof: rfl

中文:
定理 coe_bot
  结论: (↑(⊥ : 既开又闭上集 α) : 集合 α) = ∅
  证明: rfl
-/
theorem coe_bot : (↑(⊥ : ClopenUpperSet α) : Set α) = ∅ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ClopenUpperSet α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (既开又闭上集 α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (ClopenUpperSet α) :=
  ⟨⊥⟩

end ClopenUpperSet
