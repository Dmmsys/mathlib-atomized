/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Injective
public import Mathlib.RingTheory.RingHom.Surjective

/-!
# Properties satisfying faithfully flat descent for rings

We show the following properties of ring homomorphisms descend under faithfully flat ring maps:

- injective
- surjective
- bijective
-/

public section

open TensorProduct

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T]

/--
lemma `Module.FaithfullyFlat.injective_of_tensorProduct` / 引理 `Module.FaithfullyFlat.injective_of_tensorProduct`

English:
lemma Module.FaithfullyFlat.injective_of_tensorProduct
  statement: [Module.FaithfullyFlat R S]
  proof: by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S otimes[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H

中文:
引理 模.忠实平坦.injective_of_tensorProduct
  结论: [模.忠实平坦 R S]
  证明: by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S otimes[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H

Depends on / 依赖: Algebra, Algebra.linearMap, AlgebraTensorModule, AlgebraTensorModule.rid, FaithfullyFlat, LinearMap, LinearMap.lTensor, Module, Module.FaithfullyFlat.lTensor_injective_iff_injective, lTensor, lTensor_injective_iff_injective, linearMap, otimes, toLinearMap
-/
lemma Module.FaithfullyFlat.injective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Injective (algebraMap S (S otimes[R] T))) :
    Function.Injective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S otimes[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H

/--
lemma `Module.FaithfullyFlat.surjective_of_tensorProduct` / 引理 `Module.FaithfullyFlat.surjective_of_tensorProduct`

English:
lemma Module.FaithfullyFlat.surjective_of_tensorProduct
  statement: [Module.FaithfullyFlat R S]
  proof: by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S otimes[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H

中文:
引理 模.忠实平坦.surjective_of_tensorProduct
  结论: [模.忠实平坦 R S]
  证明: by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S otimes[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H

Depends on / 依赖: Algebra, Algebra.linearMap, AlgebraTensorModule, AlgebraTensorModule.rid, FaithfullyFlat, LinearMap, LinearMap.lTensor, Module, Module.FaithfullyFlat.lTensor_surjective_iff_surjective, lTensor, lTensor_surjective_iff_surjective, linearMap, otimes, toLinearMap
-/
lemma Module.FaithfullyFlat.surjective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Surjective (algebraMap S (S otimes[R] T))) :
    Function.Surjective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S otimes[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H

/--
lemma `Module.FaithfullyFlat.bijective_of_tensorProduct` / 引理 `Module.FaithfullyFlat.bijective_of_tensorProduct`

English:
lemma Module.FaithfullyFlat.bijective_of_tensorProduct
  statement: [Module.FaithfullyFlat R S]
  proof: ⟨injective_of_tensorProduct H.1, surjective_of_tensorProduct H.2⟩

中文:
引理 模.忠实平坦.bijective_of_tensorProduct
  结论: [模.忠实平坦 R S]
  证明: ⟨injective_of_tensorProduct H.1, surjective_of_tensorProduct H.2⟩

Depends on / 依赖: injective_of_tensorProduct, surjective_of_tensorProduct
-/
lemma Module.FaithfullyFlat.bijective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Bijective (algebraMap S (S otimes[R] T))) :
    Function.Bijective (algebraMap R T) :=
  ⟨injective_of_tensorProduct H.1, surjective_of_tensorProduct H.2⟩

end

/--
lemma `RingHom.FaithfullyFlat.codescendsAlong_injective` / 引理 `RingHom.FaithfullyFlat.codescendsAlong_injective`

English:
lemma RingHom.FaithfullyFlat.codescendsAlong_injective
  proof: by
  apply CodescendsAlong.mk _ injective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.injective_of_tensorProduct H

中文:
引理 环态射.忠实平坦.codescendsAlong_injective
  证明: by
  apply CodescendsAlong.mk _ injective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.injective_of_tensorProduct H

Depends on / 依赖: CodescendsAlong, CodescendsAlong.mk, faithfullyFlat_algebraMap_iff, h.injective_of_tensorProduct, injective_of_tensorProduct, injective_respectsIso, introv
-/
lemma RingHom.FaithfullyFlat.codescendsAlong_injective :
    CodescendsAlong (fun f => Function.Injective f) FaithfullyFlat := by
  apply CodescendsAlong.mk _ injective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.injective_of_tensorProduct H

/--
lemma `RingHom.FaithfullyFlat.codescendsAlong_surjective` / 引理 `RingHom.FaithfullyFlat.codescendsAlong_surjective`

English:
lemma RingHom.FaithfullyFlat.codescendsAlong_surjective
  proof: by
  apply CodescendsAlong.mk _ surjective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.surjective_of_tensorProduct H

universe u

中文:
引理 环态射.忠实平坦.codescendsAlong_surjective
  证明: by
  apply CodescendsAlong.mk _ surjective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.surjective_of_tensorProduct H

universe u

Depends on / 依赖: CodescendsAlong, CodescendsAlong.mk, faithfullyFlat_algebraMap_iff, h.surjective_of_tensorProduct, introv, surjective_of_tensorProduct, surjective_respectsIso
-/
lemma RingHom.FaithfullyFlat.codescendsAlong_surjective :
    CodescendsAlong (fun f => Function.Surjective f) FaithfullyFlat := by
  apply CodescendsAlong.mk _ surjective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.surjective_of_tensorProduct H

universe u

/--
lemma `RingHom.FaithfullyFlat.codescendsAlong_bijective` / 引理 `RingHom.FaithfullyFlat.codescendsAlong_bijective`

English:
lemma RingHom.FaithfullyFlat.codescendsAlong_bijective
  proof: CodescendsAlong.and codescendsAlong_injective codescendsAlong_surjective

中文:
引理 环态射.忠实平坦.codescendsAlong_bijective
  证明: CodescendsAlong.and codescendsAlong_injective codescendsAlong_surjective

Depends on / 依赖: CodescendsAlong, CodescendsAlong.and, codescendsAlong_injective, codescendsAlong_surjective
-/
lemma RingHom.FaithfullyFlat.codescendsAlong_bijective :
    CodescendsAlong (fun f => Function.Bijective f) FaithfullyFlat :=
  CodescendsAlong.and codescendsAlong_injective codescendsAlong_surjective
