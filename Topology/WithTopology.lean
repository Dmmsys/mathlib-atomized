/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Gemini CLI
-/
module

public import Mathlib.Topology.Defs.Induced

/-!
# Basic lemmas and instances about the `WithTopology` type synonym

`WithTopology X t` is a copy of `X` equipped with the topology `t`.
This is useful for providing multiple topologies on the same type
without causing instance conflicts.

In this file we setup basic API about this type
and transfer instances (basic, order) from `X` to `WithTopology X t`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures
and `WithLp` for metric structures.
-/

public section

variable {X : Type*} (t : TopologicalSpace X)

namespace WithTopology

/--
lemma `ofTopology_toTopology` / 引理 `ofTopology_toTopology`

English:
lemma ofTopology_toTopology
  given: (x : X)
  statement: ofTopology (toTopology t x) = x
  proof: rfl

@[simp]

中文:
引理 ofTopology_toTopology
  条件: (x : X)
  结论: ofTopology (toTopology t x) = x
  证明: rfl

@[simp]
-/
lemma ofTopology_toTopology (x : X) : ofTopology (toTopology t x) = x := rfl

@[simp]
/--
lemma `toTopology_ofTopology` / 引理 `toTopology_ofTopology`

English:
lemma toTopology_ofTopology
  given: (x : WithTopology X t)
  proof: rfl

中文:
引理 toTopology_ofTopology
  条件: (x : With拓扑 X t)
  证明: rfl
-/
lemma toTopology_ofTopology (x : WithTopology X t) :
  toTopology t (ofTopology x) = x := rfl

/--
lemma `ofTopology_surjective` / 引理 `ofTopology_surjective`

English:
lemma ofTopology_surjective
  statement: Function.Surjective (ofTopology (t := t))
  proof: Function.RightInverse.surjective ofTopology_toTopology _

中文:
引理 ofTopology_surjective
  结论: 函数.满射 (ofTopology (t := t))
  证明: Function.RightInverse.surjective ofTopology_toTopology _
-/
lemma ofTopology_surjective : Function.Surjective (ofTopology (t := t)) :=
Function.RightInverse.surjective ofTopology_toTopology _

/--
lemma `toTopology_surjective` / 引理 `toTopology_surjective`

English:
lemma toTopology_surjective
  statement: Function.Surjective (toTopology t)
  proof: Function.RightInverse.surjective toTopology_ofTopology _

中文:
引理 toTopology_surjective
  结论: 函数.满射 (toTopology t)
  证明: Function.RightInverse.surjective toTopology_ofTopology _

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, surjective, toTopology_ofTopology
-/
lemma toTopology_surjective : Function.Surjective (toTopology t) :=
Function.RightInverse.surjective toTopology_ofTopology _

/--
lemma `ofTopology_injective` / 引理 `ofTopology_injective`

English:
lemma ofTopology_injective
  statement: Function.Injective (ofTopology (t := t))
  proof: Function.LeftInverse.injective toTopology_ofTopology _

中文:
引理 ofTopology_injective
  结论: 函数.单射 (ofTopology (t := t))
  证明: Function.LeftInverse.injective toTopology_ofTopology _
-/
lemma ofTopology_injective : Function.Injective (ofTopology (t := t)) :=
Function.LeftInverse.injective toTopology_ofTopology _

/--
lemma `toTopology_injective` / 引理 `toTopology_injective`

English:
lemma toTopology_injective
  statement: Function.Injective (toTopology t)
  proof: Function.LeftInverse.injective ofTopology_toTopology _

中文:
引理 toTopology_injective
  结论: 函数.单射 (toTopology t)
  证明: Function.LeftInverse.injective ofTopology_toTopology _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, ofTopology_toTopology
-/
lemma toTopology_injective : Function.Injective (toTopology t) :=
Function.LeftInverse.injective ofTopology_toTopology _

/--
lemma `ofTopology_bijective` / 引理 `ofTopology_bijective`

English:
lemma ofTopology_bijective
  statement: Function.Bijective (ofTopology (t := t))
  proof: ⟨ofTopology_injective t, ofTopology_surjective t⟩

中文:
引理 ofTopology_bijective
  结论: 函数.双射 (ofTopology (t := t))
  证明: ⟨ofTopology_injective t, ofTopology_surjective t⟩
-/
lemma ofTopology_bijective : Function.Bijective (ofTopology (t := t)) :=
  ⟨ofTopology_injective t, ofTopology_surjective t⟩

/--
lemma `toTopology_bijective` / 引理 `toTopology_bijective`

English:
lemma toTopology_bijective
  statement: Function.Bijective (toTopology t)
  proof: ⟨toTopology_injective t, toTopology_surjective t⟩

中文:
引理 toTopology_bijective
  结论: 函数.双射 (toTopology t)
  证明: ⟨toTopology_injective t, toTopology_surjective t⟩

Depends on / 依赖: toTopology_injective, toTopology_surjective
-/
lemma toTopology_bijective : Function.Bijective (toTopology t) :=
  ⟨toTopology_injective t, toTopology_surjective t⟩

/--
lemma `toTopology_inj` / 引理 `toTopology_inj`

English:
lemma toTopology_inj
  given: {x y : X}
  statement: toTopology t x = toTopology t y ↔ x = y
  proof: (toTopology_injective t).eq_iff

中文:
引理 toTopology_inj
  条件: {x y : X}
  结论: toTopology t x = toTopology t y ↔ x = y
  证明: (toTopology_injective t).eq_iff

Depends on / 依赖: eq_iff, toTopology_injective
-/
lemma toTopology_inj {x y : X} : toTopology t x = toTopology t y ↔ x = y :=
  (toTopology_injective t).eq_iff

/--
lemma `ofTopology_inj` / 引理 `ofTopology_inj`

English:
lemma ofTopology_inj
  given: {x y : WithTopology X t}
  statement: ofTopology x = ofTopology y ↔ x = y
  proof: (ofTopology_injective t).eq_iff

中文:
引理 ofTopology_inj
  条件: {x y : With拓扑 X t}
  结论: ofTopology x = ofTopology y ↔ x = y
  证明: (ofTopology_injective t).eq_iff
-/
@[simp] lemma ofTopology_inj {x y : WithTopology X t} : ofTopology x = ofTopology y ↔ x = y :=
  (ofTopology_injective t).eq_iff

open Topology

/--
lemma `isOpen_iff` / 引理 `isOpen_iff`

English:
lemma isOpen_iff
  given: {s : Set (WithTopology X t)}
  proof: .rfl

中文:
引理 isOpen_iff
  条件: {s : 集合 (With拓扑 X t)}
  证明: .rfl
-/
lemma isOpen_iff {s : Set (WithTopology X t)} :
    IsOpen s ↔ IsOpen[t] (toTopology t ⁻¹' s) :=
  .rfl

/--
lemma `isClosed_iff` / 引理 `isClosed_iff`

English:
lemma isClosed_iff
  given: {s : Set (WithTopology X t)}
  proof: by
  simp [← isOpen_compl_iff, isOpen_iff]

中文:
引理 isClosed_iff
  条件: {s : 集合 (With拓扑 X t)}
  证明: by
  simp [← isOpen_compl_iff, isOpen_iff]

Depends on / 依赖: isOpen_compl_iff, isOpen_iff
-/
lemma isClosed_iff {s : Set (WithTopology X t)} :
    IsClosed s ↔ IsClosed[t] (toTopology t ⁻¹' s) := by
  simp [← isOpen_compl_iff, isOpen_iff]

/--
lemma `continuous_toTopology` / 引理 `continuous_toTopology`

English:
lemma continuous_toTopology
  statement: Continuous[t, _] (toTopology t)
  proof: ⟨fun _ => (·)⟩

中文:
引理 continuous_toTopology
  结论: 连续[t, _] (toTopology t)
  证明: ⟨fun _ => (·)⟩
-/
lemma continuous_toTopology : Continuous[t, _] (toTopology t) :=
  ⟨fun _ => (·)⟩

/--
lemma `continuous_ofTopology` / 引理 `continuous_ofTopology`

English:
lemma continuous_ofTopology
  statement: Continuous[_, t] (ofTopology (t := t))
  proof: ⟨fun _ => (·)⟩

中文:
引理 continuous_ofTopology
  结论: 连续[_, t] (ofTopology (t := t))
  证明: ⟨fun _ => (·)⟩
-/
lemma continuous_ofTopology : Continuous[_, t] (ofTopology (t := t)) :=
  ⟨fun _ => (·)⟩

/-! ### Set-theoretic lemmas -/

open Set

/--
lemma `image_ofTopology` / 引理 `image_ofTopology`

English:
lemma image_ofTopology
  given: (s : Set (WithTopology X t))
  statement: ofTopology '' s = toTopology t ⁻¹' s
  proof: .symm.image_symm_eq_preimage _ WithTopology.equiv X t

中文:
引理 image_ofTopology
  条件: (s : 集合 (With拓扑 X t))
  结论: ofTopology '' s = toTopology t ⁻¹' s
  证明: .symm.image_symm_eq_preimage _ WithTopology.equiv X t

Depends on / 依赖: WithTopology, WithTopology.equiv, image_symm_eq_preimage, symm.image_symm_eq_preimage
-/
lemma image_ofTopology (s : Set (WithTopology X t)) : ofTopology '' s = toTopology t ⁻¹' s :=
.symm.image_symm_eq_preimage _ WithTopology.equiv X t

/--
lemma `preimage_toTopology` / 引理 `preimage_toTopology`

English:
lemma preimage_toTopology
  given: (s : Set (WithTopology X t))
  statement: toTopology t ⁻¹' s = ofTopology '' s
  proof: (image_ofTopology t s).symm

中文:
引理 preimage_toTopology
  条件: (s : 集合 (With拓扑 X t))
  结论: toTopology t ⁻¹' s = ofTopology '' s
  证明: (image_ofTopology t s).symm

Depends on / 依赖: image_ofTopology
-/
lemma preimage_toTopology (s : Set (WithTopology X t)) : toTopology t ⁻¹' s = ofTopology '' s :=
  (image_ofTopology t s).symm

/--
lemma `image_toTopology` / 引理 `image_toTopology`

English:
lemma image_toTopology
  given: (s : Set X)
  statement: toTopology t '' s = ofTopology ⁻¹' s
  proof: .symm.image_eq_preimage_symm _ WithTopology.equiv X t

中文:
引理 image_toTopology
  条件: (s : 集合 X)
  结论: toTopology t '' s = ofTopology ⁻¹' s
  证明: .symm.image_eq_preimage_symm _ WithTopology.equiv X t

Depends on / 依赖: WithTopology, WithTopology.equiv, image_eq_preimage_symm, symm.image_eq_preimage_symm
-/
lemma image_toTopology (s : Set X) : toTopology t '' s = ofTopology ⁻¹' s :=
.symm.image_eq_preimage_symm _ WithTopology.equiv X t

/--
lemma `preimage_ofTopology` / 引理 `preimage_ofTopology`

English:
lemma preimage_ofTopology
  given: (s : Set X)
  statement: ofTopology ⁻¹' s = toTopology t '' s
  proof: (image_toTopology t s).symm

中文:
引理 preimage_ofTopology
  条件: (s : 集合 X)
  结论: ofTopology ⁻¹' s = toTopology t '' s
  证明: (image_toTopology t s).symm

Depends on / 依赖: image_toTopology
-/
lemma preimage_ofTopology (s : Set X) : ofTopology ⁻¹' s = toTopology t '' s :=
  (image_toTopology t s).symm


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: X] : Nonempty (WithTopology X t)
  body: (WithTopology.equiv X t).nonempty

中文:
实例 [非空
  签名: X] : 非空 (With拓扑 X t)
  定义体: (WithTopology.equiv X t).nonempty

Depends on / 依赖: WithTopology, WithTopology.equiv, nonempty
-/
instance [Nonempty X] : Nonempty (WithTopology X t) :=
  (WithTopology.equiv X t).nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: X] : Inhabited (WithTopology X t)
  body: ⟨toTopology t default⟩

中文:
实例 [可居
  签名: X] : 可居 (With拓扑 X t)
  定义体: ⟨toTopology t default⟩

Depends on / 依赖: toTopology
-/
instance [Inhabited X] : Inhabited (WithTopology X t) :=
  ⟨toTopology t default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: X] : Subsingleton (WithTopology X t)
  body: (WithTopology.equiv X t).subsingleton

中文:
实例 [子单例
  签名: X] : 子单例 (With拓扑 X t)
  定义体: (WithTopology.equiv X t).subsingleton

Depends on / 依赖: WithTopology, WithTopology.equiv, subsingleton
-/
instance [Subsingleton X] : Subsingleton (WithTopology X t) :=
  (WithTopology.equiv X t).subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: X] : Unique (WithTopology X t)
  body: .mk' _

中文:
实例 [唯一
  签名: X] : 唯一 (With拓扑 X t)
  定义体: .mk' _
-/
instance [Unique X] : Unique (WithTopology X t) := .mk' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: X] : Finite (WithTopology X t)
  body: .of_equiv _ (WithTopology.equiv X t).symm

中文:
实例 [有限
  签名: X] : 有限 (With拓扑 X t)
  定义体: .of_equiv _ (WithTopology.equiv X t).symm

Depends on / 依赖: WithTopology, WithTopology.equiv, of_equiv
-/
instance [Finite X] : Finite (WithTopology X t) := .of_equiv _ (WithTopology.equiv X t).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: X] : Infinite (WithTopology X t)
  body: .of_injective _ toTopology_injective _

中文:
实例 [无限
  签名: X] : 无限 (With拓扑 X t)
  定义体: .of_injective _ toTopology_injective _

Depends on / 依赖: of_injective, toTopology_injective
-/
instance [Infinite X] : Infinite (WithTopology X t) := .of_injective _ toTopology_injective _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: X] : Fintype (WithTopology X t)
  body: .ofBijective (.toTopology t) (toTopology_bijective t)

deriving instance DecidableEq for WithTopology

中文:
实例 [有限类型
  签名: X] : 有限类型 (With拓扑 X t)
  定义体: .ofBijective (.toTopology t) (toTopology_bijective t)

deriving instance DecidableEq for WithTopology

Depends on / 依赖: ofBijective, toTopology, toTopology_bijective
-/
instance [Fintype X] : Fintype (WithTopology X t) :=
  .ofBijective (.toTopology t) (toTopology_bijective t)

deriving instance DecidableEq for WithTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: X] : LE (WithTopology X t) where
  body: ofTopology x <= ofTopology y

中文:
实例 [LE
  签名: X] : LE (With拓扑 X t) where
  定义体: ofTopology x <= ofTopology y

Depends on / 依赖: ofTopology
-/
instance [LE X] : LE (WithTopology X t) where
  le x y := ofTopology x <= ofTopology y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: X] : LT (WithTopology X t) where
  body: ofTopology x < ofTopology y

中文:
实例 [LT
  签名: X] : LT (With拓扑 X t) where
  定义体: ofTopology x < ofTopology y

Depends on / 依赖: ofTopology
-/
instance [LT X] : LT (WithTopology X t) where
  lt x y := ofTopology x < ofTopology y

-- TODO: `inferInstance` works here, but it shouldn't
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: X] [DecidableLE X] : DecidableLE (WithTopology X t)
  body: fun x y =>
  inferInstanceAs (Decidable (x.ofTopology <= y.ofTopology))

中文:
实例 [LE
  签名: X] [DecidableLE X] : DecidableLE (With拓扑 X t)
  定义体: fun x y =>
  inferInstanceAs (Decidable (x.ofTopology <= y.ofTopology))
-/
instance [LE X] [DecidableLE X] : DecidableLE (WithTopology X t) := fun x y =>
  inferInstanceAs (Decidable (x.ofTopology <= y.ofTopology))

-- TODO: `inferInstance` works here, but it shouldn't
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: X] [DecidableLT X] : DecidableLT (WithTopology X t)
  body: fun x y =>
  inferInstanceAs (Decidable (x.ofTopology < y.ofTopology))

中文:
实例 [LT
  签名: X] [DecidableLT X] : DecidableLT (With拓扑 X t)
  定义体: fun x y =>
  inferInstanceAs (Decidable (x.ofTopology < y.ofTopology))
-/
instance [LT X] [DecidableLT X] : DecidableLT (WithTopology X t) := fun x y =>
  inferInstanceAs (Decidable (x.ofTopology < y.ofTopology))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: X] : Preorder (WithTopology X t)
  body: .lift ofTopology

中文:
实例 [预序
  签名: X] : 预序 (With拓扑 X t)
  定义体: .lift ofTopology

Depends on / 依赖: ofTopology
-/
instance [Preorder X] : Preorder (WithTopology X t) :=
  .lift ofTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: X] : PartialOrder (WithTopology X t)
  body: .partialOrder _ .rfl .rfl ofTopology_injective t

@[to_dual]

中文:
实例 [偏序
  签名: X] : 偏序 (With拓扑 X t)
  定义体: .partialOrder _ .rfl .rfl ofTopology_injective t

@[to_dual]

Depends on / 依赖: ofTopology_injective, partialOrder
-/
instance [PartialOrder X] : PartialOrder (WithTopology X t) :=
.partialOrder _ .rfl .rfl ofTopology_injective t

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Max
  signature: X] : Max (WithTopology X t) where
  body: toTopology t (max x.ofTopology y.ofTopology)

@[to_dual]

中文:
实例 [最大值
  签名: X] : 最大值 (With拓扑 X t) where
  定义体: toTopology t (max x.ofTopology y.ofTopology)

@[to_dual]

Depends on / 依赖: ofTopology, toTopology, x.ofTopology, y.ofTopology
-/
instance [Max X] : Max (WithTopology X t) where
  max x y := toTopology t (max x.ofTopology y.ofTopology)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeSup
  signature: X] : SemilatticeSup (WithTopology X t)
  body: .semilatticeSup _ .rfl .rfl fun _ _ => rfl ofTopology_injective t

中文:
实例 [SemilatticeSup
  签名: X] : SemilatticeSup (With拓扑 X t)
  定义体: .semilatticeSup _ .rfl .rfl fun _ _ => rfl ofTopology_injective t

Depends on / 依赖: ofTopology_injective, semilatticeSup
-/
instance [SemilatticeSup X] : SemilatticeSup (WithTopology X t) :=
.semilatticeSup _ .rfl .rfl fun _ _ => rfl ofTopology_injective t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: X] : Lattice (WithTopology X t) where

中文:
实例 [格
  签名: X] : 格 (With拓扑 X t) where
-/
instance [Lattice X] : Lattice (WithTopology X t) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribLattice
  signature: X] : DistribLattice (WithTopology X t) where
  body: le_sup_inf (α := X)

中文:
实例 [Distrib格
  签名: X] : Distrib格 (With拓扑 X t) where
  定义体: le_sup_inf (α := X)

Depends on / 依赖: le_sup_inf
-/
instance [DistribLattice X] : DistribLattice (WithTopology X t) where
  le_sup_inf _ _ _ := le_sup_inf (α := X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ord
  signature: X] : Ord (WithTopology X t) where
  body: compare x.ofTopology y.ofTopology

中文:
实例 [序
  签名: X] : 序 (With拓扑 X t) where
  定义体: compare x.ofTopology y.ofTopology

Depends on / 依赖: compare, ofTopology, x.ofTopology, y.ofTopology
-/
instance [Ord X] : Ord (WithTopology X t) where
  compare x y := compare x.ofTopology y.ofTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: X] : LinearOrder (WithTopology X t)
  body: .linearOrder _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ofTopology_injective t

中文:
实例 [线性序
  签名: X] : 线性序 (With拓扑 X t)
  定义体: .linearOrder _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ofTopology_injective t

Depends on / 依赖: linearOrder, ofTopology_injective
-/
instance [LinearOrder X] : LinearOrder (WithTopology X t) :=
.linearOrder _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ofTopology_injective t

end WithTopology
