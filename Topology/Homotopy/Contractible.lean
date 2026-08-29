/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Contractible spaces

In this file, we define `ContractibleSpace`, a space that is homotopy equivalent to `Unit`.
-/

@[expose] public section

noncomputable section

namespace ContinuousMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/--
Definition of `Nullhomotopic` / `Nullhomotopic` 的定义

English:
definition Nullhomotopic
  signature: (f : C(X, Y))
  body: exists y : Y, Homotopic f (ContinuousMap.const _ y)

中文:
定义 Nullhomotopic
  签名: (f : C(X, Y))
  定义体: exists y : Y, Homotopic f (ContinuousMap.const _ y)

Depends on / 依赖: ContinuousMap, ContinuousMap.const, Homotopic
-/
def Nullhomotopic (f : C(X, Y)) : Prop :=
  exists y : Y, Homotopic f (ContinuousMap.const _ y)

/--
theorem `nullhomotopic_of_constant` / 定理 `nullhomotopic_of_constant`

English:
theorem nullhomotopic_of_constant
  given: (y : Y)
  statement: Nullhomotopic (ContinuousMap.const X y)
  proof: ⟨y, by rfl⟩

中文:
定理 nullhomotopic_of_constant
  条件: (y : Y)
  结论: Nullhomotopic (连续映射.const X y)
  证明: ⟨y, by rfl⟩
-/
theorem nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y) :=
  ⟨y, by rfl⟩

/--
theorem `Nullhomotopic.comp_right` / 定理 `Nullhomotopic.comp_right`

English:
theorem Nullhomotopic.comp_right
  given: {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z))
  proof: by
  obtain ⟨y, hy⟩ := hf
  use g y
  exact .comp (.refl g) hy

中文:
定理 Nullhomotopic.comp_right
  条件: {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z))
  证明: by
  obtain ⟨y, hy⟩ := hf
  use g y
  exact .comp (.refl g) hy
-/
theorem Nullhomotopic.comp_right {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z)) :
    (g.comp f).Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  use g y
  exact .comp (.refl g) hy

/--
theorem `Nullhomotopic.comp_left` / 定理 `Nullhomotopic.comp_left`

English:
theorem Nullhomotopic.comp_left
  given: {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y))
  proof: by
  obtain ⟨y, hy⟩ := hf
  use y
  exact .comp hy (.refl g)

中文:
定理 Nullhomotopic.comp_left
  条件: {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y))
  证明: by
  obtain ⟨y, hy⟩ := hf
  use y
  exact .comp hy (.refl g)
-/
theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) :
    (f.comp g).Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  use y
  exact .comp hy (.refl g)

end ContinuousMap

open ContinuousMap

/--
Definition of `ContractibleSpace` / `ContractibleSpace` 的定义

English:
class ContractibleSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - hequiv_unit' : Nonempty (X ≃ₕ Unit)

中文:
类 余ntractible空间
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (1 个):
    - hequiv_unit' : 非空 (X ≃ₕ 单元)
-/
class ContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  hequiv_unit' : Nonempty (X ≃ₕ Unit)

/--
theorem `ContractibleSpace.hequiv_unit` / 定理 `ContractibleSpace.hequiv_unit`

English:
theorem ContractibleSpace.hequiv_unit
  given: (X : Type*) [TopologicalSpace X] [ContractibleSpace X]
  proof: ContractibleSpace.hequiv_unit'

中文:
定理 余ntractible空间.hequiv_unit
  条件: (X : 类型) [拓扑空间 X] [余ntractible空间 X]
  证明: ContractibleSpace.hequiv_unit'

Depends on / 依赖: ContractibleSpace, ContractibleSpace.hequiv_unit, hequiv_unit
-/
theorem ContractibleSpace.hequiv_unit (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    Nonempty (X ≃ₕ Unit) :=
  ContractibleSpace.hequiv_unit'

/--
theorem `id_nullhomotopic` / 定理 `id_nullhomotopic`

English:
theorem id_nullhomotopic
  given: (X : Type*) [TopologicalSpace X] [ContractibleSpace X]
  proof: by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.invFun ()
  convert! hv.left_inv.symm

中文:
定理 id_nullhomotopic
  条件: (X : 类型) [拓扑空间 X] [余ntractible空间 X]
  证明: by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.invFun ()
  convert! hv.left_inv.symm

Depends on / 依赖: ContractibleSpace, ContractibleSpace.hequiv_unit, convert, hequiv_unit, hv.invFun, hv.left_inv.symm, invFun, left_inv
-/
theorem id_nullhomotopic (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    (ContinuousMap.id X).Nullhomotopic := by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.invFun ()
  convert! hv.left_inv.symm

/--
theorem `contractible_iff_id_nullhomotopic` / 定理 `contractible_iff_id_nullhomotopic`

English:
theorem contractible_iff_id_nullhomotopic
  given: (Y : Type*) [TopologicalSpace Y]
  proof: by
  constructor
  · intro
    apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine
    { hequiv_unit' :=
        ⟨{ toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p
            left_inv := ?_
            right_inv := ?_ }⟩ }
  · exact h.symm
  · convert! Homotopic.refl (ContinuousMap.id Unit)

中文:
定理 contractible_iff_id_nullhomotopic
  条件: (Y : 类型) [拓扑空间 Y]
  证明: by
  constructor
  · intro
    apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine
    { hequiv_unit' :=
        ⟨{ toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p
            left_inv := ?_
            right_inv := ?_ }⟩ }
  · exact h.symm
  · convert! Homotopic.refl (ContinuousMap.id Unit)

Depends on / 依赖: ContinuousMap, ContinuousMap.const, ContinuousMap.id, Homotopic, Homotopic.refl, convert, h.symm, hequiv_unit, id_nullhomotopic, invFun, left_inv, right_inv
-/
theorem contractible_iff_id_nullhomotopic (Y : Type*) [TopologicalSpace Y] :
    ContractibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic := by
  constructor
  · intro
    apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine
    { hequiv_unit' :=
        ⟨{ toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p
            left_inv := ?_
            right_inv := ?_ }⟩ }
  · exact h.symm
  · convert! Homotopic.refl (ContinuousMap.id Unit)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
theorem `ContinuousMap.HomotopyEquiv.contractibleSpace` / 定理 `ContinuousMap.HomotopyEquiv.contractibleSpace`

English:
theorem ContinuousMap.HomotopyEquiv.contractibleSpace
  given: [ContractibleSpace Y] (e : X ≃ₕ Y)
  proof: ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩

中文:
定理 连续映射.同伦等价.contractibleSpace
  条件: [余ntractible空间 Y] (e : X ≃ₕ Y)
  证明: ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩
-/
protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace [ContractibleSpace Y] (e : X ≃ₕ Y) :
    ContractibleSpace X :=
  ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩

/--
theorem `ContinuousMap.HomotopyEquiv.contractibleSpace_iff` / 定理 `ContinuousMap.HomotopyEquiv.contractibleSpace_iff`

English:
theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff
  given: (e : X ≃ₕ Y)
  proof: ⟨fun _ => e.symm.contractibleSpace, fun _ => e.contractibleSpace⟩

中文:
定理 连续映射.同伦等价.contractibleSpace_iff
  条件: (e : X ≃ₕ Y)
  证明: ⟨fun _ => e.symm.contractibleSpace, fun _ => e.contractibleSpace⟩
-/
protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff (e : X ≃ₕ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  ⟨fun _ => e.symm.contractibleSpace, fun _ => e.contractibleSpace⟩

/--
theorem `Homeomorph.contractibleSpace` / 定理 `Homeomorph.contractibleSpace`

English:
theorem Homeomorph.contractibleSpace
  given: [ContractibleSpace Y] (e : X ≃ₜ Y)
  proof: e.toHomotopyEquiv.contractibleSpace

中文:
定理 同胚.contractibleSpace
  条件: [余ntractible空间 Y] (e : X ≃ₜ Y)
  证明: e.toHomotopyEquiv.contractibleSpace
-/
protected theorem Homeomorph.contractibleSpace [ContractibleSpace Y] (e : X ≃ₜ Y) :
    ContractibleSpace X :=
  e.toHomotopyEquiv.contractibleSpace

/--
theorem `Homeomorph.contractibleSpace_iff` / 定理 `Homeomorph.contractibleSpace_iff`

English:
theorem Homeomorph.contractibleSpace_iff
  given: (e : X ≃ₜ Y)
  proof: e.toHomotopyEquiv.contractibleSpace_iff

中文:
定理 同胚.contractibleSpace_iff
  条件: (e : X ≃ₜ Y)
  证明: e.toHomotopyEquiv.contractibleSpace_iff
-/
protected theorem Homeomorph.contractibleSpace_iff (e : X ≃ₜ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  e.toHomotopyEquiv.contractibleSpace_iff

/--
lemma `homotopic_of_indiscrete` / 引理 `homotopic_of_indiscrete`

English:
lemma homotopic_of_indiscrete
  given: [IndiscreteTopology Y] (f g : C(X, Y))
  statement: f.Homotopic g
  proof: ⟨⟨fun (t, a) => if t = 0 then f a else g a, continuous_of_indiscreteTopology⟩, by simp, by simp⟩

中文:
引理 homotopic_of_indiscrete
  条件: [Indiscrete拓扑 Y] (f g : C(X, Y))
  结论: f.同伦 g
  证明: ⟨⟨fun (t, a) => if t = 0 then f a else g a, continuous_of_indiscreteTopology⟩, by simp, by simp⟩

Depends on / 依赖: continuous_of_indiscreteTopology
-/
lemma homotopic_of_indiscrete [IndiscreteTopology Y] (f g : C(X, Y)) : f.Homotopic g :=
  ⟨⟨fun (t, a) => if t = 0 then f a else g a, continuous_of_indiscreteTopology⟩, by simp, by simp⟩

/--
lemma `nullhomotopic_of_indiscrete` / 引理 `nullhomotopic_of_indiscrete`

English:
lemma nullhomotopic_of_indiscrete
  given: [Nonempty Y] [IndiscreteTopology Y] (f : C(X, Y))
  proof: by
  inhabit Y
  use default
  exact homotopic_of_indiscrete _ _

中文:
引理 nullhomotopic_of_indiscrete
  条件: [非空 Y] [Indiscrete拓扑 Y] (f : C(X, Y))
  证明: by
  inhabit Y
  use default
  exact homotopic_of_indiscrete _ _

Depends on / 依赖: homotopic_of_indiscrete, inhabit
-/
lemma nullhomotopic_of_indiscrete [Nonempty Y] [IndiscreteTopology Y] (f : C(X, Y)) :
    f.Nullhomotopic := by
  inhabit Y
  use default
  exact homotopic_of_indiscrete _ _

namespace ContractibleSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: Y] [Subsingleton Y] : ContractibleSpace Y
  body: let ⟨_⟩ := nonempty_unique Y
  ⟨⟨(Homeomorph.homeomorphOfUnique Y Unit).toHomotopyEquiv⟩⟩

中文:
实例 [非空
  签名: Y] [子单例 Y] : 余ntractible空间 Y
  定义体: let ⟨_⟩ := nonempty_unique Y
  ⟨⟨(Homeomorph.homeomorphOfUnique Y Unit).toHomotopyEquiv⟩⟩

Depends on / 依赖: Homeomorph, Homeomorph.homeomorphOfUnique, homeomorphOfUnique, nonempty_unique, toHomotopyEquiv
-/
instance [Nonempty Y] [Subsingleton Y] : ContractibleSpace Y :=
  let ⟨_⟩ := nonempty_unique Y
  ⟨⟨(Homeomorph.homeomorphOfUnique Y Unit).toHomotopyEquiv⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: Y] [IndiscreteTopology Y] : ContractibleSpace Y
  body: (contractible_iff_id_nullhomotopic Y).mpr (nullhomotopic_of_indiscrete _)

中文:
实例 [非空
  签名: Y] [Indiscrete拓扑 Y] : 余ntractible空间 Y
  定义体: (contractible_iff_id_nullhomotopic Y).mpr (nullhomotopic_of_indiscrete _)

Depends on / 依赖: contractible_iff_id_nullhomotopic, nullhomotopic_of_indiscrete
-/
instance [Nonempty Y] [IndiscreteTopology Y] : ContractibleSpace Y :=
  (contractible_iff_id_nullhomotopic Y).mpr (nullhomotopic_of_indiscrete _)

variable (X Y) in
/--
theorem `hequiv` / 定理 `hequiv`

English:
theorem hequiv
  given: [ContractibleSpace X] [ContractibleSpace Y]
  proof: by
  rcases ContractibleSpace.hequiv_unit' (X := X) with ⟨h⟩
  rcases ContractibleSpace.hequiv_unit' (X := Y) with ⟨h'⟩
  exact ⟨h.trans h'.symm⟩

中文:
定理 hequiv
  条件: [余ntractible空间 X] [余ntractible空间 Y]
  证明: by
  rcases ContractibleSpace.hequiv_unit' (X := X) with ⟨h⟩
  rcases ContractibleSpace.hequiv_unit' (X := Y) with ⟨h'⟩
  exact ⟨h.trans h'.symm⟩

Depends on / 依赖: ContractibleSpace, ContractibleSpace.hequiv_unit, h.trans, hequiv_unit
-/
theorem hequiv [ContractibleSpace X] [ContractibleSpace Y] :
    Nonempty (X ≃ₕ Y) := by
  rcases ContractibleSpace.hequiv_unit' (X := X) with ⟨h⟩
  rcases ContractibleSpace.hequiv_unit' (X := Y) with ⟨h'⟩
  exact ⟨h.trans h'.symm⟩

instance (priority := 100) [ContractibleSpace X] : PathConnectedSpace X := by
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X
  have : forall x, Joined p x := fun x => ⟨(h.evalAt x).symm⟩
  rw [pathConnectedSpace_iff_eq]; use p; ext; tauto

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContractibleSpace
  signature: X] [ContractibleSpace Y] : ContractibleSpace (X × Y)
  body: by
  obtain ⟨hX⟩ := hequiv_unit' (X := X)
  obtain ⟨hY⟩ := hequiv_unit' (X := Y)
  refine ⟨⟨(hX.prodCongr hY).trans ?_⟩⟩
  exact (Homeomorph.prodUnique Unit Unit).toHomotopyEquiv

中文:
实例 [余ntractible空间
  签名: X] [余ntractible空间 Y] : 余ntractible空间 (X × Y)
  定义体: by
  obtain ⟨hX⟩ := hequiv_unit' (X := X)
  obtain ⟨hY⟩ := hequiv_unit' (X := Y)
  refine ⟨⟨(hX.prodCongr hY).trans ?_⟩⟩
  exact (Homeomorph.prodUnique Unit Unit).toHomotopyEquiv

Depends on / 依赖: Homeomorph, Homeomorph.prodUnique, hX.prodCongr, hequiv_unit, prodCongr, prodUnique, toHomotopyEquiv
-/
instance [ContractibleSpace X] [ContractibleSpace Y] : ContractibleSpace (X × Y) := by
  obtain ⟨hX⟩ := hequiv_unit' (X := X)
  obtain ⟨hY⟩ := hequiv_unit' (X := Y)
  refine ⟨⟨(hX.prodCongr hY).trans ?_⟩⟩
  exact (Homeomorph.prodUnique Unit Unit).toHomotopyEquiv

end ContractibleSpace
