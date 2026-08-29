/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.SeparablyGenerated

/-!

# Smooth algebras over fields

We show that separably generated extensions of fields are smooth.
In particular finitely generated field extensions over perfect fields are smooth.

-/

public section

variable {K L ι : Type*} [Field L] [Field K] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
/--
lemma `Algebra.FormallySmooth.adjoin_of_algebraicIndependent` / 引理 `Algebra.FormallySmooth.adjoin_of_algebraicIndependent`

English:
lemma Algebra.FormallySmooth.adjoin_of_algebraicIndependent
  statement: {v : ι -> L}
  proof: by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

中文:
引理 代数.形式光滑.adjoin_of_algebraicIndependent
  结论: {v : ι -> L}
  证明: by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

Depends on / 依赖: Algebra, Algebra.FormallySmooth, CompactSpace, FormallySmooth, IntermediateField, IntermediateField.adjoin, ParacompactSpace, Set.range, adjoin, aevalEquiv, hb.aevalEquiv, nonZeroDivisors, of_equiv, of_isLocalization, paracompact_of_compact
-/
lemma Algebra.FormallySmooth.adjoin_of_algebraicIndependent {v : ι -> L}
    (hb : AlgebraicIndependent K v) :
    Algebra.FormallySmooth K (IntermediateField.adjoin K (Set.range v)) := by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

/--
lemma `Algebra.FormallySmooth.of_algebraicIndependent` / 引理 `Algebra.FormallySmooth.of_algebraicIndependent`

English:
lemma Algebra.FormallySmooth.of_algebraicIndependent
  statement: {v : ι -> L}
  proof: by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

中文:
引理 代数.形式光滑.of_algebraicIndependent
  结论: {v : ι -> L}
  证明: by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

Depends on / 依赖: Algebra, Algebra.FormallySmooth.adjoin_of_algebraicIndependent, FormallySmooth, IntermediateField, IntermediateField.topEquiv, adjoin_of_algebraicIndependent, of_equiv, topEquiv
-/
lemma Algebra.FormallySmooth.of_algebraicIndependent {v : ι -> L}
    (hb : AlgebraicIndependent K v) (hb' : IntermediateField.adjoin K (Set.range v) = ⊤) :
    Algebra.FormallySmooth K L := by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

/--
lemma `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` / 引理 `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable`

English:
lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
  proof: by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

中文:
引理 代数.形式光滑.of_algebraicIndependent_of_isSeparable
  证明: by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

Depends on / 依赖: Algebra, Algebra.FormallyEtale.of_isSeparable, FormallyEtale, FormallySmooth, FormallySmooth.adjoin_of_algebraicIndependent, IntermediateField, IntermediateField.adjoin, Set.range, adjoin, adjoin_of_algebraicIndependent, of_isSeparable
-/
lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
    {v : ι -> L} (hb : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L := by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

instance (priority := low) Algebra.FormallySmooth.of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K L] : Algebra.FormallySmooth K L := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have : Algebra.IsSeparable (↥(IntermediateField.adjoin K (Set.range ((↑) : s -> L)))) L := by
    convert! H <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1
