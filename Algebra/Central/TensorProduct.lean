/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!

# Lemmas about tensor products of central algebras

In this file we prove for algebras `B` and `C` over a field `K` that if `B ⊗[K] C` is a central
algebra and `B, C` nontrivial, then both `B` and `C` are central algebras.

## Main Results

- `Algebra.IsCentral.left_of_tensor_of_field`: If `B` `C` are `K`-algebras where `K` is a field,
  `C` is nontrivial and `B ⊗[K] C` is a central algebra over `K`, then `B` is a
  central algebra over `K`.
- `Algebra.IsCentral.right_of_tensor_of_field`: If `B` `C` are `K`-algebras where `K` is a field,
  `B` is nontrivial and `B ⊗[K] C` is a central algebra over `K`, then `C` is a
  central algebra over `K`.

## Tags
Central Algebras, Central Simple Algebras, Noncommutative Algebra
-/

public section

universe u v

open TensorProduct

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

/--
lemma `Algebra.TensorProduct.includeLeft_map_center_le` / 引理 `Algebra.TensorProduct.includeLeft_map_center_le`

English:
lemma Algebra.TensorProduct.includeLeft_map_center_le
  proof: by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

中文:
引理 Algebra.TensorProduct.includeLeft_map_center_le
  证明: by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, SemiRingCat, Subalgebra, Subalgebra.mem_center_iff, Subalgebra.mem_map, TensorProduct, TensorProduct.induction_on, add_mul, induction_on, mem_center_iff, mem_map, mul_add
-/
lemma Algebra.TensorProduct.includeLeft_map_center_le :
    (Subalgebra.center K B).map includeLeft <= Subalgebra.center K (B otimes[K] C) := by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

/--
lemma `Algebra.TensorProduct.includeRight_map_center_le` / 引理 `Algebra.TensorProduct.includeRight_map_center_le`

English:
lemma Algebra.TensorProduct.includeRight_map_center_le
  proof: fun x hx => by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

中文:
引理 Algebra.TensorProduct.includeRight_map_center_le
  证明: fun x hx => by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

Depends on / 依赖: Subalgebra, Subalgebra.mem_center_iff, Subalgebra.mem_map, TensorProduct, TensorProduct.induction_on, add_mul, induction_on, mem_center_iff, mem_map, mul_add
-/
lemma Algebra.TensorProduct.includeRight_map_center_le :
    (Subalgebra.center K C).map includeRight <= Subalgebra.center K (B otimes[K] C) := fun x hx => by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

namespace Algebra.IsCentral

open Algebra.TensorProduct in
/--
lemma `left_of_tensor` / 引理 `left_of_tensor`

English:
lemma left_of_tensor
  statement: (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
  proof: (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ => ⟨k, includeLeft_injective (S := K) inj hk⟩

中文:
引理 left_of_tensor
  结论: (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
  证明: (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ => ⟨k, includeLeft_injective (S := K) inj hk⟩

Depends on / 依赖: Subalgebra, Subalgebra.map_le.mp, f.hom, includeLeft_map_center_le, map_le
-/
lemma left_of_tensor (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
    [hbc : Algebra.IsCentral K (B otimes[K] C)] : IsCentral K B where
  out := (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ => ⟨k, includeLeft_injective (S := K) inj hk⟩

/--
lemma `right_of_tensor` / 引理 `right_of_tensor`

English:
lemma right_of_tensor
  statement: (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
  proof: have : IsCentral K (C otimes[K] B) := IsCentral.of_algEquiv K _ _ Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B inj

中文:
引理 right_of_tensor
  结论: (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
  证明: have : IsCentral K (C otimes[K] B) := IsCentral.of_algEquiv K _ _ Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B inj

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, IsCentral, IsCentral.of_algEquiv, TensorProduct, left_of_tensor, of_algEquiv, otimes
-/
lemma right_of_tensor (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
    [Algebra.IsCentral K (B otimes[K] C)] : IsCentral K C :=
have : IsCentral K (C otimes[K] B) := IsCentral.of_algEquiv K _ _ Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B inj

/--
lemma `left_of_tensor_of_field` / 引理 `left_of_tensor_of_field`

English:
lemma left_of_tensor_of_field
  statement: (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial C]
  proof: left_of_tensor K B C FaithfulSMul.algebraMap_injective K C

中文:
引理 left_of_tensor_of_field
  结论: (K B C : 类型) [Field K] [Ring B] [Ring C] [Nontrivial C]
  证明: left_of_tensor K B C FaithfulSMul.algebraMap_injective K C

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, left_of_tensor
-/
lemma left_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial C]
    [Algebra K B] [Algebra K C] [IsCentral K (B otimes[K] C)] : IsCentral K B :=
left_of_tensor K B C FaithfulSMul.algebraMap_injective K C

/--
lemma `right_of_tensor_of_field` / 引理 `right_of_tensor_of_field`

English:
lemma right_of_tensor_of_field
  statement: (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial B]
  proof: right_of_tensor K B C FaithfulSMul.algebraMap_injective K B

中文:
引理 right_of_tensor_of_field
  结论: (K B C : 类型) [Field K] [Ring B] [Ring C] [Nontrivial B]
  证明: right_of_tensor K B C FaithfulSMul.algebraMap_injective K B

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, right_of_tensor
-/
lemma right_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial B]
    [Algebra K B] [Algebra K C] [IsCentral K (B otimes[K] C)] : IsCentral K C :=
right_of_tensor K B C FaithfulSMul.algebraMap_injective K B


end Algebra.IsCentral
