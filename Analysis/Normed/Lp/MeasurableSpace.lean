/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable space structure on `WithLp`

If `X` is a measurable space, we set the measurable space structure on `WithLp p X` to be the
same as the one on `X`.
-/

@[expose] public section

open scoped ENNReal

variable (p : Real>=0∞) (X : Type*) [MeasurableSpace X]

namespace WithLp

/--
Instance `measurableSpace` / 实例 `measurableSpace`

English:
instance measurableSpace
  signature: : MeasurableSpace (WithLp p X)
  body: MeasurableSpace.comap ofLp inferInstance

@[fun_prop]

中文:
实例 measurableSpace
  签名: : 可测空间 (WithLp p X)
  定义体: MeasurableSpace.comap ofLp inferInstance

@[fun_prop]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap
-/
instance measurableSpace : MeasurableSpace (WithLp p X) :=
  MeasurableSpace.comap ofLp inferInstance

@[fun_prop]
/--
lemma `measurable_ofLp` / 引理 `measurable_ofLp`

English:
lemma measurable_ofLp
  statement: Measurable (@ofLp p X)
  proof: comap_measurable _

@[fun_prop]

中文:
引理 measurable_ofLp
  结论: 可测 (@ofLp p X)
  证明: comap_measurable _

@[fun_prop]

Depends on / 依赖: comap_measurable
-/
lemma measurable_ofLp : Measurable (@ofLp p X) := comap_measurable _

@[fun_prop]
/--
lemma `measurable_toLp` / 引理 `measurable_toLp`

English:
lemma measurable_toLp
  statement: Measurable (@toLp p X)
  proof: fun s hs => by
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [Set.preimage_preimage]

中文:
引理 measurable_toLp
  结论: 可测 (@toLp p X)
  证明: fun s hs => by
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [Set.preimage_preimage]

Depends on / 依赖: Set.preimage_preimage, preimage_preimage
-/
lemma measurable_toLp : Measurable (@toLp p X) := fun s hs => by
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [Set.preimage_preimage]

variable (Y : Type*) [MeasurableSpace Y] [TopologicalSpace X] [TopologicalSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopologyEither X Y]

/--
Instance `borelSpace` / 实例 `borelSpace`

English:
instance borelSpace
  signature: : BorelSpace (WithLp p (X × Y)) where
  body: by
    rw [instProdTopologicalSpace]; rw [borel_comap]; rw [measurableSpace]; rw [BorelSpace.measurable_eq (α := X × Y)]

中文:
实例 borelSpace
  签名: : Borel空间 (WithLp p (X × Y)) where
  定义体: by
    rw [instProdTopologicalSpace]; rw [borel_comap]; rw [measurableSpace]; rw [BorelSpace.measurable_eq (α := X × Y)]

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq, borel_comap, instProdTopologicalSpace, measurableSpace, measurable_eq
-/
instance borelSpace : BorelSpace (WithLp p (X × Y)) where
  measurable_eq := by
    rw [instProdTopologicalSpace]; rw [borel_comap]; rw [measurableSpace]; rw [BorelSpace.measurable_eq (α := X × Y)]

end WithLp

namespace PiLp

variable {ι : Type*} {X : ι -> Type*} [Countable ι] [forall i, MeasurableSpace (X i)]
    [forall i, TopologicalSpace (X i)] [forall i, BorelSpace (X i)] [forall i, SecondCountableTopology (X i)]

/--
Instance `borelSpace` / 实例 `borelSpace`

English:
instance borelSpace
  signature: : BorelSpace (PiLp p X) where
  body: by
    rw [topologicalSpace]; rw [borel_comap]; rw [WithLp.measurableSpace]; rw [BorelSpace.measurable_eq (α := Π i]; rw [X i)]

中文:
实例 borelSpace
  签名: : Borel空间 (PiLp p X) where
  定义体: by
    rw [topologicalSpace]; rw [borel_comap]; rw [WithLp.measurableSpace]; rw [BorelSpace.measurable_eq (α := Π i]; rw [X i)]

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq, WithLp, WithLp.measurableSpace, borel_comap, measurableSpace, measurable_eq, topologicalSpace
-/
instance borelSpace : BorelSpace (PiLp p X) where
  measurable_eq := by
    rw [topologicalSpace]; rw [borel_comap]; rw [WithLp.measurableSpace]; rw [BorelSpace.measurable_eq (α := Π i]; rw [X i)]

end PiLp

namespace MeasurableEquiv

/--
Definition of `toLp` / `toLp` 的定义

English:
definition toLp
  signature: : X ≃ᵐ (WithLp p X) where
  body: (WithLp.equiv p X).symm
  measurable_toFun := WithLp.measurable_toLp p X
  measurable_invFun := WithLp.measurable_ofLp p X

中文:
定义 toLp
  签名: : X ≃ᵐ (WithLp p X) where
  定义体: (WithLp.equiv p X).symm
  measurable_toFun := WithLp.measurable_toLp p X
  measurable_invFun := WithLp.measurable_ofLp p X
-/
protected def toLp : X ≃ᵐ (WithLp p X) where
  toEquiv := (WithLp.equiv p X).symm
  measurable_toFun := WithLp.measurable_toLp p X
  measurable_invFun := WithLp.measurable_ofLp p X

/--
lemma `coe_toLp` / 引理 `coe_toLp`

English:
lemma coe_toLp
  statement: ⇑(MeasurableEquiv.toLp p X) = WithLp.toLp p
  proof: rfl

中文:
引理 coe_toLp
  结论: ⇑(可测等价.toLp p X) = WithLp.toLp p
  证明: rfl
-/
lemma coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithLp.toLp p := rfl

/--
lemma `coe_toLp_symm` / 引理 `coe_toLp_symm`

English:
lemma coe_toLp_symm
  statement: ⇑(MeasurableEquiv.toLp p X).symm = WithLp.ofLp
  proof: rfl

@[simp]

中文:
引理 coe_toLp_symm
  结论: ⇑(可测等价.toLp p X).symm = WithLp.ofLp
  证明: rfl

@[simp]
-/
lemma coe_toLp_symm : ⇑(MeasurableEquiv.toLp p X).symm = WithLp.ofLp := rfl

@[simp]
/--
lemma `toLp_apply` / 引理 `toLp_apply`

English:
lemma toLp_apply
  given: (x : X)
  statement: MeasurableEquiv.toLp p X x = WithLp.toLp p x
  proof: rfl

@[simp]

中文:
引理 toLp_apply
  条件: (x : X)
  结论: 可测等价.toLp p X x = WithLp.toLp p x
  证明: rfl

@[simp]
-/
lemma toLp_apply (x : X) : MeasurableEquiv.toLp p X x = WithLp.toLp p x := rfl

@[simp]
/--
lemma `toLp_symm_apply` / 引理 `toLp_symm_apply`

English:
lemma toLp_symm_apply
  given: (x : WithLp p X)
  proof: rfl

中文:
引理 toLp_symm_apply
  条件: (x : WithLp p X)
  证明: rfl
-/
lemma toLp_symm_apply (x : WithLp p X) :
    (MeasurableEquiv.toLp p X).symm x = WithLp.ofLp x := rfl

end MeasurableEquiv
